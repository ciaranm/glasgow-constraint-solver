cmake_minimum_required(VERSION 3.21)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

project(
        Glasgow-Constraint-Solver
        VERSION 0.0.1
        DESCRIPTION "An auditable constraint programming and optimisation solver"
        HOMEPAGE_URL "https://github.com/ciaranm/glasgow-constraint-solver"
        LANGUAGES CXX)

include(GNUInstallDirs)

# Build type configuration.
# Three types are supported: Release (default), Debug, and Sanitize.
# See CMakePresets.json and the README for usage.
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()
set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS Release Debug Sanitize)

# Per-type flags.  These are applied automatically by CMake for the active build type,
# on top of the always-on flags set below.
#
# Release: full optimisation, no sanitizers.  -march=native is added later after the
#   compiler capability check.  We omit -DNDEBUG deliberately because the codebase does
#   not use assert(), so it buys nothing while making behaviour harder to reason about.
set(CMAKE_CXX_FLAGS_RELEASE         "-O3"
    CACHE STRING "Flags for release builds")
# Debug: disable optimisation so the debugger can follow every step.
set(CMAKE_CXX_FLAGS_DEBUG           "-O0"
    CACHE STRING "Flags for debug builds")
# Sanitize: light optimisation keeps stack traces readable; -O0 is too slow and hides
#   inlining bugs.  ASan + UBSan together catch memory errors and undefined behaviour.
set(CMAKE_CXX_FLAGS_SANITIZE
    "-O1 -fsanitize=address,undefined -fno-omit-frame-pointer"
    CACHE STRING "Flags for sanitizer builds (ASan + UBSan)")
set(CMAKE_EXE_LINKER_FLAGS_SANITIZE    "-fsanitize=address,undefined"
    CACHE STRING "Linker flags for sanitizer builds")
set(CMAKE_SHARED_LINKER_FLAGS_SANITIZE "-fsanitize=address,undefined"
    CACHE STRING "Linker flags for sanitizer builds")

option(GCS_ENABLE_DOXYGEN "Add a doxygen target to generate the documentation" OFF)
option(GCS_ENABLE_XCSP "Support for the XCSP modelling language" ${PROJECT_IS_TOP_LEVEL})
option(GCS_ENABLE_MINIZINC "Support for the MiniZinc modelling language" ${PROJECT_IS_TOP_LEVEL})
option(GCS_ENABLE_EXAMPLES "Build examples" ${PROJECT_IS_TOP_LEVEL})
option(GCS_BUILD_TESTS "Build GCS tests" ${PROJECT_IS_TOP_LEVEL})

# Compiler flag checks always run so results are available for target-specific use.
include(CheckCXXCompilerFlag)
unset(COMPILER_SUPPORTS_MARCH_NATIVE CACHE)
CHECK_CXX_COMPILER_FLAG(-march=native COMPILER_SUPPORTS_MARCH_NATIVE)

unset(COMPILER_SUPPORTS_NO_RESTRICT CACHE)
CHECK_CXX_COMPILER_FLAG(-Wno-restrict COMPILER_SUPPORTS_NO_RESTRICT)

unset(COMPILER_SUPPORTS_NO_STRINGOP_OVERREAD CACHE)
CHECK_CXX_COMPILER_FLAG(-Wno-stringop-overread COMPILER_SUPPORTS_NO_STRINGOP_OVERREAD)

unset(COMPILER_SUPPORTS_NO_UNQUALIFIED_STD_CAST_CALL CACHE)
CHECK_CXX_COMPILER_FLAG(-Wno-unqualified-std-cast-call COMPILER_SUPPORTS_NO_UNQUALIFIED_STD_CAST_CALL)

# Global compile/link options only apply when building as the top-level project.
# When embedded as a subproject via FetchContent the parent controls these settings.
if(PROJECT_IS_TOP_LEVEL)
    add_compile_options(-W)
    add_compile_options(-Wall)

    if(COMPILER_SUPPORTS_NO_RESTRICT)
        add_compile_options(-Wno-restrict) # https://gcc.gnu.org/bugzilla/show_bug.cgi?id=104336
    endif()
    if(COMPILER_SUPPORTS_NO_STRINGOP_OVERREAD)
        add_compile_options(-Wno-stringop-overread) # https://gcc.gnu.org/bugzilla/show_bug.cgi?id=104336
    endif()
    if(COMPILER_SUPPORTS_NO_UNQUALIFIED_STD_CAST_CALL)
        add_compile_options(-Wno-unqualified-std-cast-call)
    endif()

    # Always include full debug info, even in release builds, so crash reports are useful.
    add_compile_options(-g)
    add_compile_options(-g3)
    add_compile_options(-gdwarf-3)
    add_compile_options(-pthread)
    add_link_options(-pthread)

    # Native CPU tuning is worthwhile for release performance but unhelpful for debugging.
    if(COMPILER_SUPPORTS_MARCH_NATIVE)
        add_compile_options($<$<CONFIG:Release>:-march=native>)
    endif()

    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
endif()

if(GCS_BUILD_TESTS)
    enable_testing()
endif()

# FetchContent dependencies declared before the subdirectories that consume them.
include(FetchContent)
set(FETCHCONTENT_QUIET FALSE)

if(GCS_BUILD_TESTS)
    FetchContent_Declare(
            Catch2
            GIT_REPOSITORY https://github.com/catchorg/Catch2.git
            GIT_TAG b670de4fe12ac7c5e858b7de3a14fb4bd18c760e # v3.4.10
    )
    FetchContent_MakeAvailable(Catch2)
endif()

if(GCS_ENABLE_EXAMPLES OR GCS_ENABLE_MINIZINC)
    FetchContent_Declare(
            cxxopts
            GIT_REPOSITORY https://github.com/jarro2783/cxxopts.git
            GIT_TAG 44380e5a44706ab7347f400698c703eb2a196202 # v3.3.1
    )
    FetchContent_MakeAvailable(cxxopts)
endif()

set(JSON_BuildTests OFF CACHE INTERNAL "")
FetchContent_Declare(
        json
        GIT_REPOSITORY https://github.com/nlohmann/json.git
        GIT_TAG 9cca280a4d0ccf0c08f47a99aa71d1b0e52f8d03 # v3.11.3
)
FetchContent_MakeAvailable(json)
FetchContent_GetProperties(json)  # sets json_SOURCE_DIR in this scope (inherited by subdirs)

add_library(gcs_fmt INTERFACE)

try_compile(GCS_COMPILER_HAS_FORMAT ${CMAKE_CURRENT_BINARY_DIR}/cmake_compile_tests ${CMAKE_CURRENT_SOURCE_DIR}/cmake_compile_tests/has_format.cc)
if(GCS_COMPILER_HAS_FORMAT)
    message("Using compiler's own <format> and <print> implementation")
    set(GCS_NEEDS_FMT FALSE)
else()
    message("Using libfmt instead of <format> and <print>")
    set(GCS_NEEDS_FMT TRUE)
    FetchContent_Declare(
            fmt
            GIT_REPOSITORY https://github.com/fmtlib/fmt.git
            GIT_TAG 40626af88bd7df9a5fb80be7b25ac85b122d6c21 # v11.2.0
    )
    FetchContent_MakeAvailable(fmt)
    target_link_libraries(gcs_fmt INTERFACE fmt::fmt)
endif()

try_compile(GCS_COMPILER_HAS_GENERATOR ${CMAKE_CURRENT_BINARY_DIR}/cmake_compile_tests ${CMAKE_CURRENT_SOURCE_DIR}/cmake_compile_tests/has_generator.cc)
if(GCS_COMPILER_HAS_GENERATOR)
    message("Using compiler's own <generator> implementation")
else()
    message("Using external <generator> implementation")
    include(ExternalProject)
    ExternalProject_Add(
            generator
            PREFIX ${CMAKE_CURRENT_BINARY_DIR}/generator
            GIT_REPOSITORY https://github.com/todoubaba/generator
            GIT_TAG a849a206f35c2447ab5e605edc5fcf44f673c628 # no release
            INSTALL_COMMAND ""
            BUILD_COMMAND ""
    )
    add_library(generator_include INTERFACE)
    target_include_directories(generator_include INTERFACE
            $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/generator/src/generator/include>
            $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>)
endif()

try_compile(GCS_COMPILER_HAS_STACKTRACE ${CMAKE_CURRENT_BINARY_DIR}/cmake_compile_tests ${CMAKE_CURRENT_SOURCE_DIR}/cmake_compile_tests/has_stacktrace.cc)
if(GCS_COMPILER_HAS_STACKTRACE)
    message("Using compiler's own <stacktrace> implementation")
else()
    message("No <stacktrace> implementation available")
endif()

add_subdirectory(gcs)

# Install rules for library consumers (ExternalProject / find_package).
include(CMakePackageConfigHelpers)

set(_gcs_install_targets glasgow_constraint_solver gcs_fmt)
if(NOT GCS_COMPILER_HAS_GENERATOR)
    list(APPEND _gcs_install_targets generator_include)
endif()

install(TARGETS ${_gcs_install_targets}
        EXPORT GlasgowConstraintSolverTargets
        ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
        LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
        RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})

install(EXPORT GlasgowConstraintSolverTargets
        FILE GlasgowConstraintSolverTargets.cmake
        NAMESPACE GlasgowConstraintSolver::
        DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/GlasgowConstraintSolver)

install(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/gcs/
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/gcs
        FILES_MATCHING PATTERN "*.hh"
        REGEX "constraints_test_utils\\.hh$" EXCLUDE)

install(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/util/
        DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}/util
        FILES_MATCHING PATTERN "*.hh")

if(NOT GCS_COMPILER_HAS_GENERATOR)
    install(DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/generator/src/generator/include/
            DESTINATION ${CMAKE_INSTALL_INCLUDEDIR}
            FILES_MATCHING PATTERN "*.hpp")
endif()

configure_package_config_file(
        ${CMAKE_CURRENT_SOURCE_DIR}/cmake/GlasgowConstraintSolverConfig.cmake.in
        ${CMAKE_CURRENT_BINARY_DIR}/GlasgowConstraintSolverConfig.cmake
        INSTALL_DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/GlasgowConstraintSolver)

write_basic_package_version_file(
        ${CMAKE_CURRENT_BINARY_DIR}/GlasgowConstraintSolverConfigVersion.cmake
        VERSION ${PROJECT_VERSION}
        COMPATIBILITY AnyNewerVersion)

install(FILES
        ${CMAKE_CURRENT_BINARY_DIR}/GlasgowConstraintSolverConfig.cmake
        ${CMAKE_CURRENT_BINARY_DIR}/GlasgowConstraintSolverConfigVersion.cmake
        DESTINATION ${CMAKE_INSTALL_LIBDIR}/cmake/GlasgowConstraintSolver)

if(GCS_ENABLE_EXAMPLES)
    add_subdirectory(examples)
    add_subdirectory(minicp_benchmarks)
    add_subdirectory(test)
endif()

if(GCS_ENABLE_DOXYGEN)
    find_package(Doxygen)
    if(DOXYGEN_FOUND)
        set(DOXYGEN_IN ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in)
        set(DOXYGEN_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)
        configure_file(${DOXYGEN_IN} ${DOXYGEN_OUT} @ONLY)
        add_custom_target(docs
                COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYGEN_OUT}
                WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
                VERBATIM)
    else()
        message("Could not find Doxygen to generate documentation")
    endif()
endif()

if(GCS_ENABLE_XCSP)
    add_subdirectory(xcsp)
endif()

if(GCS_ENABLE_MINIZINC)
    add_subdirectory(minizinc)
endif()

if(GCS_ENABLE_PYTHON)
    add_subdirectory(python)
endif()
