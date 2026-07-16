cmake_minimum_required(VERSION 3.16)

set(CMAKE_C_COMPILER clang)
set(CMAKE_CXX_COMPILER clang++)

project(svm_compiler CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Debug)
endif()
message(STATUS "Build Type: ${CMAKE_BUILD_TYPE}")
message(STATUS "Compiler:   ${CMAKE_CXX_COMPILER}")

set(CMAKE_CXX_FLAGS_DEBUG "-g -O0")
set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG")

add_compile_options(
    -Wall -Wextra -Wpedantic
    -Werror
    -Wno-unused-parameter
    -Wno-gnu-zero-variadic-macro-arguments
    -fno-rtti
    -fno-exceptions
)

# Export compile_commands.json
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

file(GLOB_RECURSE ALL_SOURCES CONFIGURE_DEPENDS "src/*.cpp")

set(MAIN_SOURCE "")
set(LIB_SOURCES "")
foreach(src IN LISTS ALL_SOURCES)
    if(src MATCHES "main\\.cpp$")
        set(MAIN_SOURCE "${src}")
    else()
        list(APPEND LIB_SOURCES "${src}")
    endif()
endforeach()

if(NOT MAIN_SOURCE)
    message(FATAL_ERROR "Cannot find main.cpp.")
endif()
if(NOT LIB_SOURCES)
    message(FATAL_ERROR "Cannot find any lib files.")
endif()

message(STATUS "Program entry: ${MAIN_SOURCE}")
list(LENGTH LIB_SOURCES LIB_COUNT)
message(STATUS "Libs: ${LIB_COUNT}")
add_library(svm_core STATIC ${LIB_SOURCES})

target_include_directories(svm_core PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/src
    ${CMAKE_CURRENT_SOURCE_DIR}/src/Utils
    ${CMAKE_CURRENT_SOURCE_DIR}/src/Frontend
    ${CMAKE_CURRENT_SOURCE_DIR}/src/IR
    ${CMAKE_CURRENT_SOURCE_DIR}/src/HIR
    ${CMAKE_CURRENT_SOURCE_DIR}/src/LIR
    ${CMAKE_CURRENT_SOURCE_DIR}/src/Backend
)

add_executable(svm ${MAIN_SOURCE})
if(CMAKE_CXX_COMPILER_ID MATCHES "Clang" OR CMAKE_CXX_COMPILER_ID MATCHES "GNU")
    target_link_libraries(svm PRIVATE "-Wl,--whole-archive" svm_core "-Wl,--no-whole-archive")
else()
    target_link_libraries(svm PRIVATE svm_core)
endif()
