#!/usr/bin/env python3
"""
test.py — SVM 编译器测试套件 (lli 解释执行 + QEMU RISC-V 后端)

功能:
  - 单文件测试: 编译 -> dump HIR/LIR/LLVM IR -> 执行 -> 查看结果
  - 批量测试: 并行跑整个测试目录, 汇总统计, 收集详细失败日志与耗时记录
  - 双后端执行:
    · 默认模式: 通过 riscv64-linux-gnu-gcc 汇编链接 + qemu-riscv64 执行
    · --lli 模式: 通过 lli 解释执行 LLVM IR
  - GCC 性能对比: 支持与 GCC 多级优化 (O0~O3) 进行性能对比
  - 故障诊断: 当结果不匹配时自动提取 LLVM IR 并在宿主机验证, 定界前端/后端 Bug
  - 浮点精度保障: GCC 参考结果使用严格浮点编译参数, 与评测机基准一致
  - 安全清理: Ctrl+C 中断时自动清理所有临时文件

前置条件:
  - 已构建 build/svm
  - 默认 RV 模式需要 riscv64-linux-gnu-gcc(g++) + qemu-riscv64
  - --lli 模式需要 lli + sylib.ll + clang
"""

from __future__ import annotations

import abc
import argparse
import atexit
import multiprocessing
import os
import shutil
import signal
import subprocess as proc
import sys
import tempfile
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from concurrent.futures.process import BrokenProcessPool
from dataclasses import dataclass
from pathlib import Path

TIMEOUT_COMPILE = 60.0
TIMEOUT_LINK = 10.0
TIMEOUT_DIAGNOSE = 30.0
TIMEOUT_BASELINE_RUN = 30.0


def safe_proc_run(*popenargs, **kwargs):
    timeout = kwargs.pop("timeout", None)
    input_data = kwargs.pop("input", None)
    capture_output = kwargs.pop("capture_output", False)
    if capture_output:
        kwargs["stdout"] = proc.PIPE
        kwargs["stderr"] = proc.PIPE
    if input_data is not None:
        kwargs["stdin"] = proc.PIPE
    if sys.platform != "win32":
        kwargs["start_new_session"] = True
    check = kwargs.pop("check", False)

    def _kill_proc(p):
        if p.poll() is not None:
            return
        try:
            if sys.platform != "win32":
                os.killpg(os.getpgid(p.pid), getattr(signal, "SIGKILL", 9))
            else:
                p.kill()
        except (OSError, ProcessLookupError):
            pass

    with proc.Popen(*popenargs, **kwargs) as process:
        try:
            stdout, stderr = process.communicate(input=input_data, timeout=timeout)
        except proc.TimeoutExpired as exc:
            _kill_proc(process)
            process.wait()
            raise proc.TimeoutExpired(
                process.args, timeout, output=exc.stdout, stderr=exc.stderr
            ) from None
        except BaseException:
            _kill_proc(process)
            try:
                process.wait(timeout=1.0)
            except proc.TimeoutExpired:
                pass
            raise
        retcode = process.poll()
        if check and retcode:
            raise proc.CalledProcessError(
                retcode, process.args, output=stdout, stderr=stderr
            )
        return proc.CompletedProcess(process.args, retcode, stdout, stderr)


if Path("/dev/shm").is_dir():
    try:
        usage = shutil.disk_usage("/dev/shm")
        if usage.free > 1024 * 1024 * 1024:
            tempfile.tempdir = "/dev/shm"
            RAMDISK_ENABLED = True
        else:
            RAMDISK_ENABLED = False
    except OSError:
        RAMDISK_ENABLED = False
else:
    RAMDISK_ENABLED = False
PROJECT_ROOT = Path(__file__).resolve().parent
BUILD_DIR = PROJECT_ROOT / "build"
TEMP_DIR = PROJECT_ROOT / "temp"
ERROR_LOG = PROJECT_ROOT / "test_errors.log"
TIMES_FILE = PROJECT_ROOT / "rank" / "time.txt"


def _find_runtime_source(name: str) -> Path:
    override = os.environ.get(f"SYLIB_{name.split('.')[-1].upper()}")
    candidates = [
        Path(override).expanduser() if override else None,
        BUILD_DIR / name,
        PROJECT_ROOT / "tests" / "runtime" / name,
    ]
    return next(
        (path for path in candidates if path and path.is_file()), BUILD_DIR / name
    )


SYLIB_PATH = _find_runtime_source("sylib.c")
SYLIB_H_PATH = _find_runtime_source("sylib.h")
SYLIB_O_PATH = BUILD_DIR / "sylib.o"
SYLIB_NATIVE_O_PATH = BUILD_DIR / "sylib_native.o"
WRAPPER_H = TEMP_DIR / "hack_wrapper.h"
RISCV_GCC = "riscv64-linux-gnu-gcc"
RISCV_GXX = "riscv64-linux-gnu-g++"
RISCV_QEMU = "qemu-riscv64"
RV_TARGET_FLAGS = ["-march=rv64gc", "-mabi=lp64d"]
STRICT_MATH_FLAGS = [
    "-ffp-contract=off",
    "-fsingle-precision-constant",
    "-fno-strict-aliasing",
    "-ffloat-store",
    "-fno-tree-vectorize",
    "-fno-associative-math",
    "-fno-builtin",
    "-fwrapv",
]


def _find_compiler() -> Path:
    override = os.environ.get("SVM_BIN")
    candidates = [
        Path(override).expanduser() if override else None,
        BUILD_DIR / "svm",
        PROJECT_ROOT / "build-ninja" / "svm",
    ]
    return next(
        (path for path in candidates if path and path.is_file()), BUILD_DIR / "svm"
    )


def _find_runtime() -> Path | None:
    override = os.environ.get("SYLIB_LL")
    candidates = [
        Path(override).expanduser() if override else None,
        BUILD_DIR / "sylib.ll",
        PROJECT_ROOT / "sylib.ll",
    ]
    return next((path for path in candidates if path and path.is_file()), None)


SVM_BIN = _find_compiler()
SYLIB_LL = _find_runtime()
LLI = os.environ.get("LLI", "lli")
_executor_ref: list[ProcessPoolExecutor | None] = [None]


def _worker_init():
    def handler(signum, frame):
        raise KeyboardInterrupt()

    signal.signal(signal.SIGINT, handler)


def _cleanup_all_temps() -> None:
    """清理全局临时目录"""
    shutil.rmtree(TEMP_DIR, ignore_errors=True)


def _is_pid_alive(pid: int) -> bool:
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
        return True
    except OSError:
        return False


def _cleanup_stale_temps() -> None:
    """启动时清理上次崩溃遗留的临时目录, 防止残留文件导致测试失败"""
    tmp_root = Path(tempfile.gettempdir())
    try:
        for entry in tmp_root.iterdir():
            if entry.is_dir() and entry.name.startswith("svm-test-"):
                parts = entry.name.split("-")
                if (
                    len(parts) >= 3
                    and parts[2].isdigit()
                    and not _is_pid_alive(int(parts[2]))
                ):
                    shutil.rmtree(entry, ignore_errors=True)
    except OSError:
        pass


_shutdown_flag = [False]


def _sigint_handler(signum, frame):
    print("\n[中断] Ctrl+C, 正在终止所有工作进程...", file=sys.stderr, flush=True)
    _shutdown_flag[0] = True
    for p in multiprocessing.active_children():
        try:
            if sys.platform != "win32":
                os.kill(p.pid, signal.SIGINT)
            else:
                p.terminate()
        except (OSError, ProcessLookupError):
            pass
    raise KeyboardInterrupt


atexit.register(_cleanup_all_temps)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="SVM 编译器测试套件 (默认 RISC-V 后端, 可选 lli 解释执行)"
    )
    p.add_argument("-t", "--test", help="单文件测试: 指定 .sy 文件路径")
    p.add_argument("-d", "--directory", help="批量测试: 指定测试目录路径")
    opt_group = p.add_mutually_exclusive_group()
    opt_group.add_argument("-O0", action="store_true", help="禁用优化 -O0")
    opt_group.add_argument("-O1", action="store_true", help="启用优化 -O1 (默认)")
    p.add_argument(
        "-S",
        "--no-link",
        action="store_true",
        help="只生成各阶段 dump / 汇编, 不链接执行",
    )
    p.add_argument(
        "-P", "--parallel", type=int, default=1, metavar="N", help="并行测试进程数"
    )
    p.add_argument("-n", "--no-execute", action="store_true", help="只编译, 不执行")
    p.add_argument("-r", "--run", action="store_true", help="执行并与标准输出比较")
    p.add_argument(
        "-C",
        "--compare",
        action="store_true",
        help="性能对比: lli 模式重复计时 / RV 模式与 GCC 交叉编译产物对决",
    )
    p.add_argument(
        "--lli",
        action="store_true",
        help="启用 LLVM lli 后端解释执行模式 (默认使用 RISC-V 后端)",
    )
    p.add_argument(
        "--target-O",
        type=int,
        nargs="+",
        choices=range(4),
        default=None,
        metavar="N",
        help="GCC 对比优化级别列表, 可多个 (如 --target-O 1 2 3); 不指定则对比 O0~O3 全级别",
    )
    p.add_argument(
        "--runs",
        type=int,
        default=1,
        metavar="N",
        help="性能测试每个用例的重复运行次数 (默认: 1); 表格同时给出 N 次的最小值与平均值, 每次运行时间写入 *_raw.json",
    )
    p.add_argument("-i", "--input", help="指定 stdin 输入文件")
    p.add_argument("--timeout", type=float, default=10.0, help="编译超时时间(秒)")
    p.add_argument(
        "--runtime-timeout", type=float, default=None, help="运行时超时时间(秒)"
    )
    p.add_argument(
        "-V", "--valgrind", action="store_true", help="通过 Valgrind 启动编译器"
    )
    p.add_argument(
        "-v", "--verbose", action="store_true", help="显示编译器命令及完整失败输出"
    )
    p.add_argument("-s", "--stats", action="store_true", help="输出测试耗时统计")
    p.add_argument(
        "--asm", help="直接测试: --lli 模式执行 .ll/.bc / 默认模式链接 .s 汇编文件"
    )
    return p.parse_args(argv)


def normalize(text: str) -> str:
    if not text:
        return ""
    return "\n".join(line.rstrip() for line in text.splitlines()).strip()


def truncate_output(text: str, limit: int = 2048) -> str:
    if not text:
        return ""
    if len(text) > limit:
        return f"{text[:limit]}\n\n... [省略后续部分, 总长度: {len(text)} 字符]"
    return text


def log_error(path: Path, kind: str, output: str) -> None:
    ERROR_LOG.parent.mkdir(parents=True, exist_ok=True)
    with ERROR_LOG.open("a", encoding="utf-8") as f:
        f.write(f"{'=' * 60}\nFile:  {path}\nType:  {kind}\n{output}\n\n")


def log_session_start() -> None:
    ERROR_LOG.parent.mkdir(parents=True, exist_ok=True)
    with ERROR_LOG.open("a", encoding="utf-8") as f:
        f.write(
            f"{'#' * 60}\n# Session started: {time.strftime('%Y-%m-%d %H:%M:%S')}\n{'#' * 60}\n\n"
        )


def log_session_end() -> None:
    try:
        with ERROR_LOG.open("a", encoding="utf-8") as f:
            f.write(
                f"{'#' * 60}\n# Session ended: {time.strftime('%Y-%m-%d %H:%M:%S')}\n{'#' * 60}\n\n"
            )
    except OSError as exc:
        log_error(
            ERROR_LOG, "log_session_end", f"Failed to write session end log: {exc}"
        )


def precompile_sylib_rv() -> None:
    """预编译运行时库, 消除并发链接时的 CPU 瓶颈, 并全局禁用相关优化以保证浮点基准一致"""
    BUILD_DIR.mkdir(parents=True, exist_ok=True)
    if not SYLIB_PATH.exists():
        sys.exit(f"[ERROR] Runtime library source not found at {SYLIB_PATH}")
    print("[INFO] Precompiling sylib.c to sylib.o (Strict FP & Aliasing Disabled) ...")
    try:
        safe_proc_run(
            [
                RISCV_GCC,
                *RV_TARGET_FLAGS,
                "-O2",
                "-c",
                str(SYLIB_PATH),
                "-o",
                str(SYLIB_O_PATH),
                *STRICT_MATH_FLAGS,
            ],
            check=True,
            stdout=proc.PIPE,
            stderr=proc.STDOUT,
            timeout=TIMEOUT_COMPILE,
        )
    except proc.CalledProcessError as e:
        sys.exit(
            f"[FATAL] Failed to precompile sylib.c:\n{e.output.decode('utf-8', errors='replace').strip()}"
        )
    except OSError as e:
        sys.exit(f"[FATAL] Exception during sylib precompilation: {e}")


def precompile_sylib_native() -> None:
    BUILD_DIR.mkdir(parents=True, exist_ok=True)
    c_compiler = os.environ.get("CC", "gcc")
    print("[INFO] Precompiling sylib.c for native baseline (GCC) ...")
    try:
        safe_proc_run(
            [
                c_compiler,
                "-x",
                "c",
                "-O1",
                *STRICT_MATH_FLAGS,
                "-w",
                "-c",
                str(SYLIB_PATH),
                "-o",
                str(SYLIB_NATIVE_O_PATH),
            ],
            check=True,
            stdout=proc.PIPE,
            stderr=proc.STDOUT,
            timeout=TIMEOUT_COMPILE,
        )
    except (OSError, proc.SubprocessError) as e:
        print(f"[WARNING] Failed to precompile native sylib: {e}", file=sys.stderr)


def generate_hack_wrapper() -> None:
    """生成 C++ 兼容的 wrapper header, 用于 GCC 编译 .sy 文件作为参考结果"""
    TEMP_DIR.mkdir(parents=True, exist_ok=True)
    wrapper_content = f'''
#ifndef _SYSY_HACK_WRAPPER_H
#define _SYSY_HACK_WRAPPER_H

#define delete sysy_delete

#ifdef __cplusplus
extern "C" {{
#endif

#include "{SYLIB_H_PATH.absolute()}"

#ifdef __cplusplus
}}
#endif

#ifdef __cplusplus
  #define getarray(arr)      ::getarray(reinterpret_cast<int*>(arr))
  #define getfarray(arr)     ::getfarray(reinterpret_cast<float*>(arr))
  #define putarray(n, arr)   ::putarray(n, reinterpret_cast<int*>(arr))
  #define putfarray(n, arr)  ::putfarray(n, reinterpret_cast<float*>(arr))
#else
  #define getarray(arr)      getarray((int*)(arr))
  #define getfarray(arr)     getfarray((float*)(arr))
  #define putarray(n, arr)   putarray(n, (int*)(arr))
  #define putfarray(n, arr)  putfarray(n, (float*)(arr))
#endif

#endif // _SYSY_HACK_WRAPPER_H
'''
    WRAPPER_H.write_text(wrapper_content)
    print(f"[INFO] Hack wrapper generated at {WRAPPER_H}")


def build_reference_executable(
    sy_path: Path, exe_path: Path, target: str, opt_level: int = 1
) -> tuple[bool, str]:
    """
    使用 GCC 编译 .sy 文件为参考可执行文件

    target: "native" (宿主机 g++) 或 "riscv" (riscv64-linux-gnu-g++)
    所有编译参数均包含 STRICT_MATH_FLAGS, 保障浮点精度与评测机基准绝对一致
    """
    if target == "native":
        compiler = os.environ.get("CXX", "g++")
        cmd = [
            compiler,
            "-x",
            "c++",
            "-fno-operator-names",
            f"-O{opt_level}",
            *STRICT_MATH_FLAGS,
            "-include",
            str(WRAPPER_H),
            str(sy_path),
            "-x",
            "none",
            str(SYLIB_NATIVE_O_PATH)
            if SYLIB_NATIVE_O_PATH.exists()
            else str(SYLIB_PATH),
            "-Wl,-z,muldefs",
            "-w",
            "-o",
            str(exe_path),
        ]
    elif target == "riscv":
        cmd = [
            RISCV_GXX,
            *RV_TARGET_FLAGS,
            "-x",
            "c++",
            "-fno-operator-names",
            f"-O{opt_level}",
            *STRICT_MATH_FLAGS,
            "-include",
            str(WRAPPER_H),
            str(sy_path),
            "-x",
            "none",
            str(SYLIB_O_PATH),
            "-Wl,-z,muldefs",
            "-static",
            "-w",
            "-o",
            str(exe_path),
        ]
    else:
        return (False, f"Unknown target: {target}")
    try:
        safe_proc_run(
            cmd,
            check=True,
            stdout=proc.PIPE,
            stderr=proc.STDOUT,
            timeout=TIMEOUT_COMPILE,
        )
        return (True, "")
    except proc.CalledProcessError as e:
        return (False, e.output.decode("utf-8", errors="replace").strip())
    except proc.TimeoutExpired:
        return (False, f"GCC Compilation Timeout ({TIMEOUT_COMPILE}s)")
    except OSError as e:
        return (False, f"Exception: {e}")


def get_or_generate_expected_output(
    sy_path: Path, in_path: Path | None, out_path: Path
) -> str | None:
    """获取预期输出优先读 .out 文件 不存在时用 native GCC 编译执行生成基准"""
    if out_path.exists():
        try:
            return out_path.read_text(encoding="utf-8").strip()
        except OSError as e:
            print(
                f"[warn] failed to read expected output {out_path}: {e}",
                file=sys.stderr,
            )
    with tempfile.TemporaryDirectory(prefix=f"svm-test-{os.getpid()}-") as tmpdir:
        exe_path = Path(tmpdir) / "baseline.out"
        success, _ = build_reference_executable(
            sy_path, exe_path, target="native", opt_level=1
        )
        if not success:
            return None
        stdin_data = in_path.read_bytes() if in_path and in_path.exists() else None
        try:
            res = safe_proc_run(
                [str(exe_path)],
                input=stdin_data,
                stdout=proc.PIPE,
                stderr=proc.DEVNULL,
                timeout=TIMEOUT_BASELINE_RUN,
                check=False,
            )
            expected = f"{res.stdout.decode('utf-8', errors='replace').strip()}\n{res.returncode}".strip()
            tmp_out = out_path.with_name(f"{out_path.name}.{os.getpid()}.tmp")
            tmp_out.write_text(expected + "\n", encoding="utf-8")
            tmp_out.replace(out_path)
            return expected
        except (OSError, proc.TimeoutExpired):
            return None


def diagnose_miscompile(
    sy_path: Path, in_path: Path | None, expected: str, enable_O0: bool = False
) -> str:
    """
    当汇编执行结果不符预期时, 由中端导出 LLVM IR 交给宿主 clang 运行
    裁定 Bug 是在 "前端/中端生成了语义错误的 IR" 还是 "后端发射了错误的机器码"
    加入防误差选项, 防止浮点 IR 节点在宿主机被非法融合
    """
    with tempfile.TemporaryDirectory(prefix=f"svm-test-{os.getpid()}-") as tmpdir:
        ll_path = Path(tmpdir) / "output.ll"
        exe_path = Path(tmpdir) / "a.out"
        try:
            cmd = [str(SVM_BIN), "-emit-lir", str(sy_path), "-o", str(ll_path)]
            if enable_O0:
                cmd.append("-O0")
            safe_proc_run(
                cmd,
                check=True,
                stdout=proc.PIPE,
                stderr=proc.STDOUT,
                timeout=TIMEOUT_COMPILE,
            )
        except (OSError, proc.TimeoutExpired, proc.CalledProcessError):
            return "Frontend: Failed to emit LLVM IR or crashed during generation."
        try:
            if not SYLIB_NATIVE_O_PATH.exists():
                return "Midend/Frontend: Diagnosis failed because sylib_native.o is missing."
            safe_proc_run(
                [
                    "clang",
                    "-O0",
                    str(ll_path),
                    str(SYLIB_NATIVE_O_PATH),
                    *STRICT_MATH_FLAGS,
                    "-lm",
                    "-o",
                    str(exe_path),
                ],
                check=True,
                stdout=proc.PIPE,
                stderr=proc.STDOUT,
                timeout=TIMEOUT_DIAGNOSE,
            )
        except (OSError, proc.TimeoutExpired, proc.CalledProcessError):
            return "Midend/Frontend: Generated invalid LLVM IR that was rejected by LLVM/Clang."
        stdin_data = in_path.read_bytes() if in_path and in_path.exists() else None
        try:
            result = safe_proc_run(
                [str(exe_path)],
                input=stdin_data,
                stdout=proc.PIPE,
                stderr=proc.DEVNULL,
                timeout=TIMEOUT_DIAGNOSE,
                check=False,
            )
            llvm_actual = f"{result.stdout.decode('utf-8', errors='replace').strip()}\n{result.returncode}".strip()
            if normalize(llvm_actual) == normalize(expected):
                return "Backend: IR is semantically correct, but RISC-V target codegen produced wrong results."
            else:
                return "Frontend/Midend: The emitted IR is semantically incorrect (output logic differs from C baseline)."
        except (OSError, proc.TimeoutExpired) as e:
            return f"Verification Error: Failed to execute IR baseline binary: {e}"


def verify_and_measure_time(
    cmd: list[str],
    stdin_data: bytes | None,
    expected_out: str,
    runs: int,
    timeout: float,
    is_valgrind: bool = False,
) -> tuple[str, float | None, float | None, list[float]]:
    """执行命令 runs 次, 第一次验证正确性, 后续仅计时

    返回 (status, min_time, avg_time, raw_times):
      - min_time: runs 次中的最小值 (与旧版行为一致)
      - avg_time: runs 次中的算术平均值
      - raw_times: 每一次的运行时间 (供方差/置信区间分析)
    """
    if runs < 1:
        return ("Invalid Runs", None, None, [])
    actual_timeout = timeout * (5 if is_valgrind else 1)
    times: list[float] = []
    try:
        start = time.perf_counter()
        res = safe_proc_run(
            cmd,
            input=stdin_data,
            stdout=proc.PIPE,
            stderr=proc.DEVNULL,
            timeout=actual_timeout,
            check=False,
        )
        times.append(time.perf_counter() - start)
        actual = f"{res.stdout.decode('utf-8', errors='replace').strip()}\n{res.returncode}".strip()
        if normalize(actual) != normalize(expected_out):
            return ("Mismatch", None, None, times)
        if res.returncode < 0:
            return (f"Crash ({res.returncode})", None, None, times)
    except proc.TimeoutExpired:
        return ("Timeout", None, None, times)
    except OSError:
        return ("Exec Err", None, None, times)
    for _ in range(runs - 1):
        try:
            start = time.perf_counter()
            res = safe_proc_run(
                cmd,
                input=stdin_data,
                stdout=proc.DEVNULL,
                stderr=proc.DEVNULL,
                timeout=actual_timeout,
                check=False,
            )
            times.append(time.perf_counter() - start)
            if res.returncode < 0:
                return (f"Crash ({res.returncode})", None, None, times)
        except proc.TimeoutExpired:
            return ("Timeout", None, None, times)
        except OSError:
            return ("Exec Err", None, None, times)
    avg = sum(times) / len(times) if times else None
    return ("OK", min(times), avg, times)


def _input_bytes(path: Path | None) -> bytes | None:
    return path.read_bytes() if path and path.is_file() else None


def _expected_output(
    source: Path, explicit_input: Path | None = None
) -> tuple[bytes | None, str | None]:
    """读取 .in / .out 文件, 返回 (stdin_bytes, expected_text)"""
    input_path = explicit_input or source.with_suffix(".in")
    output_path = source.with_suffix(".out")
    expected = (
        output_path.read_text(encoding="utf-8").strip()
        if output_path.is_file()
        else None
    )
    return (_input_bytes(input_path), expected)


def _get_task_weight(sy_path: Path) -> int:
    """按文件大小估算任务权重, 用于调度大任务优先"""
    weight = sy_path.stat().st_size if sy_path.exists() else 0
    in_path = sy_path.with_suffix(".in")
    if in_path.exists():
        weight += in_path.stat().st_size
    out_path = sy_path.with_suffix(".out")
    if out_path.exists():
        weight += out_path.stat().st_size
    return weight


@dataclass(frozen=True)
class CaseResult:
    source: Path
    error: str | None
    elapsed: float | None
    log_content: tuple[str, str] | None = None


def _run_batch(
    worker_fn, payloads: list, total: int, workers: int, label_fn
) -> list[CaseResult]:
    """
    通用的批量执行引擎: 支持串行和并行模式, 统一进度输出
    worker_fn: 接受单个 payload, 返回 CaseResult
    label_fn: 从 CaseResult 提取显示标签
    """
    results: list[CaseResult] = []
    if workers <= 1:
        for i, payload in enumerate(payloads, 1):
            result = worker_fn(payload)
            results.append(result)
            if result.log_content:
                log_error(result.source, result.log_content[0], result.log_content[1])
            status = "[PASS]" if result.error is None else "[FAIL]"
            print(f"[{i}/{total}] {label_fn(result)} ... {status}", flush=True)
        return results
    executor = ProcessPoolExecutor(max_workers=workers, initializer=_worker_init)
    _executor_ref[0] = executor
    try:
        futures = {executor.submit(worker_fn, payload): payload for payload in payloads}
        for i, future in enumerate(as_completed(futures), 1):
            try:
                result = future.result()
            except Exception as e:  # noqa: BLE001
                payload = futures[future]
                source = payload[0]
                result = CaseResult(source, f"Worker crashed: {e}", None)
            results.append(result)
            if result.log_content:
                log_error(result.source, result.log_content[0], result.log_content[1])
            status = "[PASS]" if result.error is None else "[FAIL]"
            print(f"[{i}/{total}] {label_fn(result)} ... {status}", flush=True)
    except KeyboardInterrupt:
        _shutdown_flag[0] = True
        print("\n[中断] Ctrl+C, 正在终止测试...", file=sys.stderr)
    except (OSError, BrokenProcessPool) as error:
        if not _shutdown_flag[0]:
            completed_sources = {r.source for r in results}
            remaining_payloads = [p for p in payloads if p[0] not in completed_sources]
            suspects = [p[0].name for p in remaining_payloads[:workers]]
            print(
                f"\n[FATAL] Process pool crashed ({type(error).__name__}: {error})! Suspects: {suspects}"
            )
            print("Falling back to serial mode to identify the faulty case...\n")
            for i, payload in enumerate(remaining_payloads, len(results) + 1):
                result = worker_fn(payload)
                results.append(result)
                if result.log_content:
                    log_error(
                        result.source, result.log_content[0], result.log_content[1]
                    )
                status = "[PASS]" if result.error is None else "[FAIL]"
                print(f"[{i}/{total}] {label_fn(result)} ... {status}", flush=True)
    finally:
        try:
            executor.shutdown(wait=False, cancel_futures=True)
        except TypeError:
            executor.shutdown(wait=False)
        _executor_ref[0] = None
    return results


def _compiler_command(
    stage: str, source: Path, output: Path, args: argparse.Namespace
) -> list[str]:
    command = [str(SVM_BIN), f"-emit-{stage}", str(source), "-o", str(output)]
    if args.O0:
        command.append("-O0")
    if args.stats:
        command.append("-time")
    if args.verbose:
        print("+", " ".join(command), flush=True)
    if args.valgrind:
        return ["valgrind", "--error-exitcode=1", *command]
    return command


def _run_checked(command: list[str], timeout: float) -> None:
    safe_proc_run(
        command, check=True, stdout=proc.PIPE, stderr=proc.STDOUT, timeout=timeout
    )


def dump_stages(
    source: Path, directory: Path, args: argparse.Namespace
) -> tuple[Path, Path, Path]:
    hir = directory / f"{source.stem}.hir"
    lir = directory / f"{source.stem}.lir"
    llvm = directory / f"{source.stem}.ll"
    for stage, output in (("hir", hir), ("lir-pre", lir), ("lir", llvm)):
        _run_checked(_compiler_command(stage, source, output, args), args.timeout)
        if not output.is_file():
            raise RuntimeError(f"compiler did not create {output}")
    return (hir, lir, llvm)


def execute_llvm(llvm: Path, stdin: bytes | None, timeout: float) -> tuple[str, float]:
    command = [LLI]
    if SYLIB_LL:
        command.append(f"--extra-module={SYLIB_LL}")
    command.append(str(llvm))
    start = time.perf_counter()
    result = safe_proc_run(
        command,
        input=stdin,
        stdout=proc.PIPE,
        stderr=proc.PIPE,
        timeout=timeout,
        check=False,
    )
    elapsed = time.perf_counter() - start
    stdout = result.stdout.decode("utf-8", errors="replace").strip()
    actual = f"{stdout}\n{result.returncode}".strip()
    if result.returncode < 0:
        raise RuntimeError(
            f"lli terminated by signal {-result.returncode}: {result.stderr.decode(errors='replace')}"
        )
    return (actual, elapsed)


def run_ir_file(path_name: str, args: argparse.Namespace) -> int:
    """直接用 lli 执行 .ll/.bc 文件"""
    path = Path(path_name).resolve()
    try:
        actual, elapsed = execute_llvm(
            path,
            _input_bytes(Path(args.input)) if args.input else None,
            args.runtime_timeout or args.timeout,
        )
        print(actual)
        if args.stats:
            print(f"lli time: {elapsed:.6f}s")
        return 0
    except (OSError, proc.SubprocessError, RuntimeError) as error:
        print(f"[FAIL] lli execution failed: {error}")
        return 1


def _rv_compile(source: Path, output: Path, args: argparse.Namespace) -> list[str]:
    """构建 SVM 编译器命令 (RV 模式: 直接生成汇编)"""
    command = [str(SVM_BIN), str(source), "-o", str(output)]
    if args.O0:
        command.append("-O0")
    if args.no_link:
        command.append("-S")
    if args.stats:
        command.append("-time")
    if args.verbose:
        print("+", " ".join(command), flush=True)
    if args.valgrind:
        return ["valgrind", "--error-exitcode=1", *command]
    return command


class TestBackend(abc.ABC):
    def __init__(self, args):
        self.args = args

    @abc.abstractmethod
    def run_single(self, source_name: str) -> int:
        pass

    @abc.abstractmethod
    def get_worker_fn(self):
        pass

    def test_all(self, label: str) -> int:
        root = Path(self.args.directory).resolve()
        cases = list(root.rglob("*.sy")) if root.is_dir() else []
        if not cases:
            print(f"No test cases found under {root}.")
            return 1
        total = len(cases)
        cases.sort(key=lambda tc: _get_task_weight(tc), reverse=True)
        workers = max(1, self.args.parallel)
        print(f"Testing {total} files ({workers} process(es), {label} mode)...")
        if RAMDISK_ENABLED:
            print("[INFO] Using /dev/shm (Ramdisk) for temporary files.")
        results = _run_batch(
            self.get_worker_fn(),
            [(case, self.args) for case in cases],
            total,
            workers,
            label_fn=lambda r: (
                str(r.source.relative_to(root))
                if r.source.is_relative_to(root)
                else r.source.name
            ),
        )
        _write_times(results)
        _print_summary(results)
        if _shutdown_flag[0]:
            return 130
        return 1 if any(r.error for r in results) else 0


class LLIBackend(TestBackend):
    def run_single(self, source_name: str) -> int:
        source = Path(source_name).resolve()
        if not source.is_file():
            print(f"[FAIL] Test file not found: {source}")
            return 1
        TEMP_DIR.mkdir(parents=True, exist_ok=True)
        try:
            hir, lir, llvm = dump_stages(source, TEMP_DIR, self.args)
            print(f"[OK] HIR: {hir}\n[OK] LIR: {lir}\n[OK] LLVM IR: {llvm}")
            if (
                self.args.no_execute
                or self.args.no_link
                or (not self.args.run and (not self.args.compare))
            ):
                return 0
            stdin_path = (
                Path(self.args.input).resolve()
                if getattr(self.args, "input", None)
                else None
            )
            stdin, expected = _expected_output(source, stdin_path)
            if expected is None:
                expected = get_or_generate_expected_output(
                    source,
                    stdin_path or source.with_suffix(".in"),
                    source.with_suffix(".out"),
                )
                if expected is None:
                    print("[WARNING] Could not get or generate expected output.")
            runs = max(1, self.args.runs or self.args.avg_n)
            timings: list[float] = []

            actual, elapsed = execute_llvm(
                llvm, stdin, self.args.runtime_timeout or self.args.timeout
            )
            timings.append(elapsed)
            if expected is not None and normalize(actual) != normalize(expected):
                print(
                    f"[FAIL] Output Mismatch\n[EXPECTED]\n{expected}\n[ACTUAL]\n{actual}"
                )
                return 1

            for _ in range(runs - 1):
                _, elapsed = execute_llvm(
                    llvm, stdin, self.args.runtime_timeout or self.args.timeout
                )
                timings.append(elapsed)
            if expected is None:
                print(f"[OK] lli execution finished.\n{actual}")
            else:
                print("[PASS] Output matches expected.")
            if self.args.compare or self.args.stats:
                avg = sum(timings) / len(timings)
                print(f"Average lli time: {avg:.6f}s ({runs} run(s))")
            return 0
        except (
            proc.CalledProcessError,
            proc.TimeoutExpired,
            RuntimeError,
            OSError,
        ) as error:
            output = getattr(error, "stdout", None)
            detail = output.decode("utf-8", errors="replace") if output else str(error)
            if isinstance(error, proc.CalledProcessError):
                print(
                    f"[FAIL] Compile Crash/Error (Exit Code {error.returncode}):\n{truncate_output(detail, 500)}"
                )
            else:
                print(f"[FAIL] Compiler Error:\n{detail}")
            return 1

    def get_worker_fn(self):
        return _lli_worker


def _lli_worker(payload) -> CaseResult:
    source, args = payload
    runtime_timeout = args.runtime_timeout or args.timeout
    try:
        with tempfile.TemporaryDirectory(prefix=f"svm-test-{os.getpid()}-") as tmp:
            _, _, llvm = dump_stages(source, Path(tmp), args)
            if args.no_execute or args.no_link:
                return CaseResult(source, None, None)
            stdin_path = (
                Path(args.input).resolve() if getattr(args, "input", None) else None
            )
            stdin, expected = _expected_output(source, stdin_path)
            if expected is None:
                expected = get_or_generate_expected_output(
                    source,
                    stdin_path or source.with_suffix(".in"),
                    source.with_suffix(".out"),
                )
                if expected is None:
                    return CaseResult(source, "missing expected .out file", None)
            actual, elapsed = execute_llvm(llvm, stdin, runtime_timeout)
            if normalize(actual) != normalize(expected):
                detail = f"Expected:\n{expected}\nActual:\n{actual}"
                bug_diag = diagnose_miscompile(
                    source, source.with_suffix(".in"), expected, args.O0
                )
                return CaseResult(
                    source,
                    f"{bug_diag}:\n{truncate_output(detail, 500)}",
                    None,
                    (bug_diag, detail),
                )
            return CaseResult(source, None, elapsed)
    except proc.TimeoutExpired as error:
        return CaseResult(source, f"Timeout: {' '.join(map(str, error.cmd))}", None)
    except proc.CalledProcessError as error:
        output = (
            error.stdout.decode("utf-8", errors="replace")
            if error.stdout
            else str(error)
        )
        return CaseResult(
            source,
            f"Compile Crash/Error (Exit Code {error.returncode}):\n{truncate_output(output, 500)}",
            None,
            ("Compile Crash", output),
        )
    except (OSError, RuntimeError) as error:
        return CaseResult(
            source, f"Exception: {error}", None, ("Exception", str(error))
        )


class RVBackend(TestBackend):
    def run_single(self, source_name: str) -> int:
        sy_path = Path(source_name).resolve()
        if not sy_path.is_file():
            print(f"[FAIL] Test file not found: {sy_path}")
            return 1
        basename = sy_path.stem
        TEMP_DIR.mkdir(parents=True, exist_ok=True)
        asm_path = TEMP_DIR / f"{basename}.s"
        command = _rv_compile(sy_path, asm_path, self.args)
        try:
            safe_proc_run(
                command,
                check=True,
                stdout=proc.PIPE,
                stderr=proc.STDOUT,
                timeout=self.args.timeout,
            )
            print("[OK] Compilation finished.")
        except proc.CalledProcessError as e:
            err_msg = e.output.decode("utf-8", errors="replace").strip()
            print(
                f"[FAIL] Compile Crash/Error (Exit Code {e.returncode}):\n{truncate_output(err_msg, 500)}"
            )
            return 1
        except (OSError, proc.TimeoutExpired) as e:
            print(f"[FAIL] Execution Exception:\n{e}")
            return 1
        if self.args.no_execute or self.args.no_link or self.args.valgrind:
            return 0
        if not (self.args.run or self.args.compare):
            return 0
        sy_dir = sy_path.parent.absolute()
        in_file = (
            Path(self.args.input).resolve()
            if getattr(self.args, "input", None)
            else sy_dir / f"{basename}.in"
        )
        out_file = sy_dir / f"{basename}.out"
        expected = get_or_generate_expected_output(sy_path, in_file, out_file)
        if expected is None:
            print("[WARNING] Could not get or generate expected output.")
            return 1
        exe_path = TEMP_DIR / basename
        try:
            safe_proc_run(
                [
                    RISCV_GCC,
                    *RV_TARGET_FLAGS,
                    str(asm_path),
                    str(SYLIB_O_PATH),
                    "-Wl,-z,muldefs",
                    "-static",
                    "-o",
                    str(exe_path),
                ],
                check=True,
                timeout=TIMEOUT_LINK,
            )
            stdin_data = in_file.read_bytes() if in_file.exists() else None
            res = safe_proc_run(
                [RISCV_QEMU, str(exe_path)],
                input=stdin_data,
                stdout=proc.PIPE,
                stderr=proc.DEVNULL,
                timeout=self.args.runtime_timeout or self.args.timeout,
                check=False,
            )
            actual = f"{res.stdout.decode('utf-8', errors='replace').strip()}\n{res.returncode}".strip()
            if normalize(actual) == normalize(expected):
                print("[PASS] Output matches expected.")
                return 0
            else:
                bug_diag = diagnose_miscompile(sy_path, in_file, expected, self.args.O0)
                disp_expected = truncate_output(expected)
                disp_actual = truncate_output(actual)
                log_error(
                    sy_path,
                    "miscompile",
                    f"Diagnosis: {bug_diag}\nExpected:\n{expected}\nActual:\n{actual}",
                )
                print(
                    f"[FAIL] Output Mismatch!\n[DIAGNOSIS] {bug_diag}\n[EXPECTED]\n{disp_expected}\n[ACTUAL]\n{disp_actual}"
                )
                return 1
        except (OSError, proc.TimeoutExpired, proc.CalledProcessError) as e:
            print(f"[FAIL] Runtime/Linkage Error: {e}")
            return 1

    def get_worker_fn(self):
        return _rv_worker


def _rv_worker(payload) -> CaseResult:
    sy_path, args = payload
    in_path = (
        Path(args.input).resolve()
        if getattr(args, "input", None)
        else sy_path.with_suffix(".in")
    )
    out_path = sy_path.with_suffix(".out")
    timeout = args.timeout
    enable_O0 = args.O0
    runtime_timeout = (
        args.runtime_timeout if args.runtime_timeout is not None else args.timeout
    )
    expected = get_or_generate_expected_output(sy_path, in_path, out_path)
    if expected is None:
        return CaseResult(sy_path, "Failed to generate baseline", None)
    try:
        with tempfile.TemporaryDirectory(prefix=f"svm-test-{os.getpid()}-") as tmpdir:
            tmp = Path(tmpdir)
            asm_path = tmp / "output.s"
            exe_path = tmp / "a.out"
            cmd = [str(SVM_BIN), str(sy_path), "-o", str(asm_path)]
            if enable_O0:
                cmd.append("-O0")
            try:
                safe_proc_run(
                    cmd,
                    check=True,
                    stdout=proc.PIPE,
                    stderr=proc.STDOUT,
                    timeout=timeout,
                )
            except proc.CalledProcessError as e:
                err_msg = e.output.decode("utf-8", errors="replace").strip()
                return CaseResult(
                    sy_path,
                    f"Compile Crash/Error (Exit Code {e.returncode}):\n{truncate_output(err_msg, 500)}",
                    None,
                    ("Compile Crash", err_msg),
                )
            except proc.TimeoutExpired:
                return CaseResult(sy_path, "Compile Timeout", None)
            try:
                safe_proc_run(
                    [
                        RISCV_GCC,
                        *RV_TARGET_FLAGS,
                        "-static",
                        str(asm_path),
                        str(SYLIB_O_PATH),
                        "-Wl,-z,muldefs",
                        "-o",
                        str(exe_path),
                    ],
                    check=True,
                    stdout=proc.PIPE,
                    stderr=proc.STDOUT,
                    timeout=TIMEOUT_LINK,
                )
            except proc.TimeoutExpired:
                return CaseResult(sy_path, "Linkage Timeout", None)
            except proc.CalledProcessError as e:
                err_msg = e.output.decode("utf-8", errors="replace").strip()
                return CaseResult(
                    sy_path,
                    f"Linkage Error:\n{err_msg}",
                    None,
                    ("Linkage Error", err_msg),
                )
            except OSError as e:
                return CaseResult(sy_path, f"Linkage Exception: {e}", None)
            stdin_data = in_path.read_bytes() if in_path and in_path.exists() else None
            try:
                start = time.perf_counter()
                result = safe_proc_run(
                    [RISCV_QEMU, str(exe_path)],
                    input=stdin_data,
                    stdout=proc.PIPE,
                    stderr=proc.DEVNULL,
                    timeout=runtime_timeout,
                    check=False,
                )
                elapsed = time.perf_counter() - start
            except proc.TimeoutExpired:
                return CaseResult(sy_path, "Runtime Timeout", None)
            except OSError as e:
                return CaseResult(sy_path, f"Runtime Exception: {e}", None)
            if result.returncode < 0:
                return CaseResult(
                    sy_path,
                    f"QEMU Crash ({result.returncode})",
                    None,
                    ("QEMU Crash", f"Exit code {result.returncode}"),
                )
            actual = f"{result.stdout.decode('utf-8', errors='replace').strip()}\n{result.returncode}".strip()
            if normalize(actual) != normalize(expected):
                bug_diag = diagnose_miscompile(sy_path, in_path, expected, enable_O0)
                err_summary = f"Output Mismatch [{bug_diag}]\nExp: {truncate_output(expected, 100)}\nAct: {truncate_output(actual, 100)}"
                return CaseResult(
                    sy_path,
                    err_summary,
                    None,
                    (
                        "miscompile",
                        f"Diagnosis: {bug_diag}\nExpected:\n{expected}\nActual:\n{actual}",
                    ),
                )
            return CaseResult(sy_path, None, elapsed)
    except OSError as e:
        return CaseResult(sy_path, f"Exception: {e}", None, ("Exception", str(e)))


def sha256_hex(data: bytes | None) -> str:
    """计算文件内容 sha256 (None/空 视为空内容, 保证 .in 缺失也可配对)"""
    import hashlib

    return hashlib.sha256(data or b"").hexdigest()


def run_benchmark_worker(
    sy_path: Path,
    bench_timeout: float,
    target_opts: list[int],
    runs: int,
    is_O0: bool = False,
) -> tuple[str, dict]:
    """对单个 .sy 文件进行 SVM vs GCC 多级优化性能对比

    返回 (输出文本, raw 数据字典)
    raw 数据含稳定主键(相对路径 + source/input sha256) 与每次运行时间, 供统计/配对分析
    """
    basename = sy_path.stem
    sy_dir = sy_path.parent
    in_file = sy_dir / f"{basename}.in"
    out_file = sy_dir / f"{basename}.out"
    expected_out = get_or_generate_expected_output(sy_path, in_file, out_file)
    if expected_out is None:
        return (
            f"[ERROR] {basename} : Cannot acquire standard output, skipping benchmark.",
            {},
        )
    stdin_data = in_file.read_bytes() if in_file.exists() else None
    src_hash = sha256_hex(sy_path.read_bytes())
    in_hash = sha256_hex(stdin_data)
    rel_id = f"{sy_path.parent.name}/{basename}"
    output_lines = [
        f"\n{'=' * 75}\n  Benchmark: {rel_id}  [src={src_hash[:12]} in={in_hash[:12]}]\n{'=' * 75}"
    ]
    raw_entry: dict = {
        "id": rel_id,
        "source_sha256": src_hash,
        "input_sha256": in_hash,
        "compilers": {},
    }
    with tempfile.TemporaryDirectory(prefix=f"svm-test-{os.getpid()}-") as tmpdir:
        tmp = Path(tmpdir)
        results: dict[str, tuple[str, float | None, float | None, list[float]]] = {}
        error_details: list[str] = []
        svm_asm = tmp / f"{basename}_svm.s"
        svm_exe = tmp / f"{basename}_svm"
        try:
            svm_cmd = [str(SVM_BIN), str(sy_path), "-o", str(svm_asm)]
            if is_O0:
                svm_cmd.append("-O0")
            safe_proc_run(
                svm_cmd,
                check=True,
                stdout=proc.PIPE,
                stderr=proc.STDOUT,
                timeout=TIMEOUT_COMPILE,
            )
            safe_proc_run(
                [
                    RISCV_GCC,
                    *RV_TARGET_FLAGS,
                    str(svm_asm),
                    str(SYLIB_O_PATH),
                    "-Wl,-z,muldefs",
                    "-static",
                    "-o",
                    str(svm_exe),
                ],
                check=True,
                stdout=proc.PIPE,
                stderr=proc.STDOUT,
                timeout=TIMEOUT_LINK,
            )
            status, t_min, t_avg, t_raw = verify_and_measure_time(
                [RISCV_QEMU, str(svm_exe)],
                stdin_data,
                expected_out,
                runs,
                bench_timeout,
            )
            results["svm"] = (status, t_min, t_avg, t_raw)
        except proc.TimeoutExpired:
            results["svm"] = ("Compile Timeout", None, None, [])
        except proc.CalledProcessError as e:
            results["svm"] = ("Compile Error", None, None, [])
            error_details.append(
                f"[{basename}] svm/gcc 编译报错:\n{e.output.decode('utf-8', errors='replace').strip()}"
            )
        except OSError:
            results["svm"] = ("Sys Exception", None, None, [])
        for opt in target_opts:
            gcc_label = f"GCC-O{opt}"
            opt_exe = tmp / f"{basename}_{gcc_label}"
            success, err_msg = build_reference_executable(
                sy_path, opt_exe, target="riscv", opt_level=opt
            )
            if success:
                status, t_min, t_avg, t_raw = verify_and_measure_time(
                    [RISCV_QEMU, str(opt_exe)],
                    stdin_data,
                    expected_out,
                    runs,
                    bench_timeout,
                )
                results[gcc_label] = (status, t_min, t_avg, t_raw)
            else:
                results[gcc_label] = ("GCC Error", None, None, [])
                error_details.append(f"[{basename}] {gcc_label} 编译失败:\n{err_msg}")
        for label, (status, t_min, t_avg, t_raw) in results.items():
            raw_entry["compilers"][label] = {
                "status": status,
                "times": t_raw,
                "min": t_min,
                "avg": t_avg,
            }
        output_lines.append(
            f"  {'Compiler':<12} {'Status':<18} {'Min (s)':>10} {'Avg (s)':>10} {'Ratio':>8} {'Rate':>8}"
        )
        output_lines.append(
            f"  {'-' * 10} {'-' * 18} {'-' * 10} {'-' * 10} {'-' * 8} {'-' * 8}"
        )
        _svm_status, svm_time, _, _ = results.get("svm", ("Unknown", None, None, []))
        display_labels = ["svm"] + [f"GCC-O{opt}" for opt in target_opts]
        for label in display_labels:
            if label not in results:
                continue
            status, t_min, t_avg, _ = results[label]
            if status != "OK" or t_min is None:
                status_str = f"[{status}]"
                output_lines.append(
                    f"  {label:<12} {status_str:<18} {'-':>10} {'-':>10} {'-':>8} {'-':>8}"
                )
            elif svm_time and svm_time > 0 and (label != "svm"):
                ratio = t_min / svm_time
                pct = ratio * 100
                avg_s = f"{t_avg:.6f}s" if t_avg is not None else "-"
                output_lines.append(
                    f"  {label:<12} {'[OK] Valid':<18} {t_min:>10.6f}s {avg_s:>10} {ratio:>8.3f} {pct:>7.1f}%"
                )
            else:
                avg_s = f"{t_avg:.6f}s" if t_avg is not None else "-"
                output_lines.append(
                    f"  {label:<12} {'[OK] Valid':<18} {t_min:>10.6f}s {avg_s:>10} {'-':>8} {'-':>8}"
                )
        if error_details:
            output_lines.append("\n[Error Details]")
            for err_text in error_details:
                output_lines.append(truncate_output(err_text, 2048))
        output_lines.append(f"{'=' * 75}")
    return "\n".join(output_lines), raw_entry


def _run_bench(args_tuple: tuple) -> tuple[str, Path, dict]:
    res_str, raw = run_benchmark_worker(*args_tuple)
    return res_str, args_tuple[0], raw


def benchmark_all(args: argparse.Namespace, target_opts: list[int]) -> int:
    """RV 模式批量性能对比 — SVM vs GCC O0~O3"""
    test_cases: list[tuple] = []
    bench_timeout = args.runtime_timeout or args.timeout
    is_O0 = getattr(args, "O0", False)
    runs = max(1, args.runs or args.avg_n or 1)
    for root, _, files in os.walk(args.directory):
        for file in files:
            if file.endswith(".sy"):
                sy_path = (Path(root) / file).resolve()
                test_cases.append((sy_path, bench_timeout, target_opts, runs, is_O0))
    total = len(test_cases)
    if total == 0:
        print("No test cases found.")
        return 1
    test_cases.sort(key=lambda x: _get_task_weight(x[0]), reverse=True)
    workers = max(1, args.parallel)
    opts_str = ", ".join(f"O{o}" for o in target_opts)
    print(
        f"Benchmarking {total} files ({workers} process(es))...\n"
        f"Targeting: GCC-[{opts_str}] "
        f"({runs} runs: min & avg; raw times in *_raw.json)\n"
    )
    output_log_dict: dict[Path | str, str] = {}
    raw_entries: list[dict] = []
    if workers > 1:
        executor = ProcessPoolExecutor(max_workers=workers, initializer=_worker_init)
        _executor_ref[0] = executor
        completed_cases = set()
        try:
            futures = {executor.submit(_run_bench, tc): tc for tc in test_cases}
            for future in as_completed(futures):
                if _shutdown_flag[0]:
                    break
                try:
                    res_str, source_path, raw = future.result()
                    completed_cases.add(source_path)
                    output_log_dict[source_path] = res_str
                    if raw:
                        raw_entries.append(raw)
                    print(res_str, flush=True)
                except Exception as error:  # noqa: BLE001
                    err_msg = f"[ERROR] Benchmark task failed: {error}"
                    output_log_dict[Path(f"error_{id(error)}")] = err_msg
                    print(err_msg, file=sys.stderr, flush=True)
        except KeyboardInterrupt:
            _shutdown_flag[0] = True
            print("\n[中断] Ctrl+C, 正在终止性能测试...", file=sys.stderr)
        except (OSError, BrokenProcessPool) as error:
            if not _shutdown_flag[0]:
                print(
                    f"\n[FATAL] Process pool crashed ({type(error).__name__}: {error})!"
                )
                print("Falling back to serial mode to identify the faulty case...\n")
                remaining_cases = [
                    tc for tc in test_cases if tc[0] not in completed_cases
                ]
                for tc in remaining_cases:
                    res_str, source_path, raw = _run_bench(tc)
                    output_log_dict[source_path] = res_str
                    if raw:
                        raw_entries.append(raw)
                    print(res_str, flush=True)
        finally:
            try:
                executor.shutdown(wait=False, cancel_futures=True)
            except TypeError:
                executor.shutdown(wait=False)
            _executor_ref[0] = None
    else:
        for tc in test_cases:
            res_str, source_path, raw = _run_bench(tc)
            output_log_dict[source_path] = res_str
            if raw:
                raw_entries.append(raw)
            print(res_str, flush=True)

    if _shutdown_flag[0]:
        print("\n[INFO] 正在保存已完成的 Benchmark 结果...", file=sys.stderr)

    final_log = []
    for tc in test_cases:
        if tc[0] in output_log_dict:
            final_log.append(output_log_dict[tc[0]])
    for key, val in output_log_dict.items():
        if isinstance(key, str) and key.startswith("error_"):
            final_log.append(val)

    rank_dir = PROJECT_ROOT / "rank"
    rank_dir.mkdir(exist_ok=True)
    with (rank_dir / "benchmark.txt").open("w", encoding="utf-8") as f:
        f.write("\n".join(final_log))

    # 保存每次运行时间 (raw samples), 供方差/置信区间/配对检验
    if raw_entries:
        import datetime
        import json

        raw_name = Path(args.directory).resolve().name
        raw_path = Path.cwd() / f"{raw_name}_raw.json"
        raw_path.write_text(
            json.dumps(
                {
                    "directory": str(Path(args.directory).resolve()),
                    "runs": runs,
                    "generated": datetime.datetime.now(datetime.timezone.utc).isoformat(
                        timespec="seconds"
                    ),
                    "cases": raw_entries,
                },
                indent=1,
                ensure_ascii=False,
            ),
            encoding="utf-8",
        )
        print(f"[INFO] Raw per-run times saved to {raw_path}", file=sys.stderr)
    return 130 if _shutdown_flag[0] else 0


def run_asm_rv(asm_file: str, args: argparse.Namespace) -> int:
    """RV 模式直接链接 .s 汇编文件并用 QEMU 执行"""
    TEMP_DIR.mkdir(parents=True, exist_ok=True)
    exe_path = TEMP_DIR / "asm_test_out"
    try:
        safe_proc_run(
            [
                RISCV_GCC,
                *RV_TARGET_FLAGS,
                asm_file,
                str(SYLIB_O_PATH),
                "-Wl,-z,muldefs",
                "-static",
                "-o",
                str(exe_path),
            ],
            check=True,
            timeout=TIMEOUT_LINK,
        )
        stdin_data = Path(args.input).read_bytes() if args.input else None
        res = safe_proc_run(
            [RISCV_QEMU, str(exe_path)],
            input=stdin_data,
            capture_output=True,
            check=False,
            timeout=args.runtime_timeout
            if args.runtime_timeout is not None
            else args.timeout,
        )
        stdout = res.stdout.decode("utf-8", errors="replace").strip()
        if stdout:
            print(stdout)
        print(f"Return code: {res.returncode}")
        return 0
    except (OSError, proc.CalledProcessError, proc.TimeoutExpired) as e:
        print(f"[FAIL] Direct ASM execution failed: {e}")
        return 1


def _write_times(results: list[CaseResult]) -> None:
    """写入耗时统计到 rank/time.txt"""
    timings = sorted(
        (r.source.name, r.elapsed) for r in results if r.elapsed is not None
    )
    TIMES_FILE.parent.mkdir(parents=True, exist_ok=True)
    TIMES_FILE.write_text(
        "".join((f"{name} {elapsed:.6f}\n" for name, elapsed in timings)),
        encoding="utf-8",
    )


def _print_summary(results: list[CaseResult]) -> None:
    """打印测试结果汇总表"""
    failures = [r for r in results if r.error]
    print(
        f"\n{'=' * 50}\n"
        f"  Total:  {len(results)}\n"
        f"  Passed: {len(results) - len(failures)}\n"
        f"  Failed: {len(failures)}\n"
        f"{'=' * 50}"
    )
    for r in sorted(failures, key=lambda item: str(item.source)):
        print(f"\n[FAIL] {r.source}\n{r.error}")


def main(argv: list[str] | None = None) -> int:
    signal.signal(signal.SIGINT, _sigint_handler)
    _cleanup_stale_temps()
    log_session_start()
    atexit.register(log_session_end)
    args = parse_args(argv)
    if args.valgrind:
        print("[INFO] Valgrind enabled, extending compile timeout to 120s.")
        args.timeout = 120.0
    if not SVM_BIN.is_file():
        print(
            f"[ERROR] Compiler binary not found at {SVM_BIN}. Set SVM_BIN to override.",
            file=sys.stderr,
        )
        return 2

    if not SYLIB_NATIVE_O_PATH.exists():
        precompile_sylib_native()
    generate_hack_wrapper()

    if not args.lli:
        for tool, name in [
            (RISCV_GCC, "riscv64-linux-gnu-gcc"),
            (RISCV_QEMU, "qemu-riscv64"),
        ]:
            if not shutil.which(tool):
                print(
                    f"[ERROR] {name} not found. Required for RV mode.", file=sys.stderr
                )
                return 2
        precompile_sylib_rv()
        if args.asm:
            return run_asm_rv(args.asm, args)
        if args.compare:
            target_opts = (
                list(args.target_O) if args.target_O is not None else [0, 1, 2, 3]
            )
            if args.directory:
                return benchmark_all(args, target_opts)
            elif args.test:
                res_str, _raw = run_benchmark_worker(
                    Path(args.test).resolve(),
                    args.runtime_timeout or args.timeout,
                    target_opts,
                    max(1, args.runs or args.avg_n or 1),
                )
                print(res_str)
                return 0
            else:
                print(
                    "[ERROR] --compare requires -t <file> or -d <directory>",
                    file=sys.stderr,
                )
                return 2
        if args.directory:
            return RVBackend(args).test_all("RV Backend")
        if args.test:
            return RVBackend(args).run_single(args.test)
        print(
            "Please specify -t (single), -d (directory), -C (benchmark), or --asm.",
            file=sys.stderr,
        )
        return 2
    if args.asm:
        return run_ir_file(args.asm, args)
    if not shutil.which(LLI):
        print(f"[ERROR] lli not found: {LLI}. Set LLI to override.", file=sys.stderr)
        return 2
    if args.directory:
        return LLIBackend(args).test_all("lli")
    if args.test:
        return LLIBackend(args).run_single(args.test)
    print(
        "Please specify -t (single), -d (directory), or --asm (LLVM IR).",
        file=sys.stderr,
    )
    return 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("\n[中断] 测试已取消", file=sys.stderr)
        raise SystemExit(130)
