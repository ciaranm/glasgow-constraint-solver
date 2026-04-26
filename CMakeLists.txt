cmake_minimum_required(VERSION 3.18)
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

project(
        Glasgow-Constraint-Solver
        VERSION 0.0.1
        DESCRIPTION "An auditable constraint programming and optimisation solver"
        HOMEPAGE_URL "https://github.com/ciaranm/glasgow-constraint-solver"
        LANGUAGES CXX)

add_compile_options(-W)
add_compile_options(-Wall)

include(CheckCXXCompilerFlag)
unset(COMPILER_SUPPORTS_MARCH_NATIVE CACHE)
CHECK_CXX_COMPILER_FLAG(-march=native COMPILER_SUPPORTS_MARCH_NATIVE)
if (COMPILER_SUPPORTS_MARCH_NATIVE)
    add_compile_options(-march=native)
endif (COMPILER_SUPPORTS_MARCH_NATIVE)

unset(COMPILER_SUPPORTS_NO_RESTRICT CACHE)
CHECK_CXX_COMPILER_FLAG(-Wno-restrict COMPILER_SUPPORTS_NO_RESTRICT)
if (COMPILER_SUPPORTS_NO_RESTRICT)
    add_compile_options(-Wno-restrict) # https://gcc.gnu.org/bugzilla/show_bug.cgi?id=104336
endif (COMPILER_SUPPORTS_NO_RESTRICT)

unset(COMPILER_SUPPORTS_NO_STRINGOP_OVERREAD CACHE)
CHECK_CXX_COMPILER_FLAG(-Wno-stringop-overread COMPILER_SUPPORTS_NO_STRINGOP_OVERREAD)
if (COMPILER_SUPPORTS_NO_STRINGOP_OVERREAD)
    add_compile_options(-Wno-stringop-overread) # https://gcc.gnu.org/bugzilla/show_bug.cgi?id=104336
endif (COMPILER_SUPPORTS_NO_STRINGOP_OVERREAD)

unset(COMPILER_SUPPORTS_NO_UNQUALIFIED_STD_CAST_CALL CACHE)
CHECK_CXX_COMPILER_FLAG(-Wno-unqualified-std-cast-call COMPILER_SUPPORTS_NO_UNQUALIFIED_STD_CAST_CALL)
if (COMPILER_SUPPORTS_NO_UNQUALIFIED_STD_CAST_CALL)
    add_compile_options(-Wno-unqualified-std-cast-call)
endif (COMPILER_SUPPORTS_NO_UNQUALIFIED_STD_CAST_CALL)

add_compile_options(-g)
add_compile_options(-g3)
add_compile_options(-gdwarf-3)
add_compile_options(-pthread)

add_link_options(-pthread)

if (NOT GCS_DEBUG_MODE)
    add_compile_options(-O3)
endif (NOT GCS_DEBUG_MODE)

enable_testing()
option(GCS_ENABLE_DOXYGEN "Add a doxygen target to generate the documentation" OFF)
option(GCS_ENABLE_XCSP "Support for the XCSP modelling language" ON)
option(GCS_ENABLE_MINIZINC "Support for the MiniZinc modelling language" ON)
option(GCS_ENABLE_EXAMPLES "Build examples" ON)
option(GCS_DEBUG_MODE "Disable compiler optimisation for debugging" OFF)

add_library(gcs_fmt INTERFACE)

try_compile(GCS_COMPILER_HAS_GENERATOR ${CMAKE_BINARY_DIR}/cmake_compile_tests ${CMAKE_SOURCE_DIR}/cmake_compile_tests/has_generator.cc)
if (GCS_COMPILER_HAS_GENERATOR)
    message("Using compiler's own <generator> implementation")
else (GCS_COMPILER_HAS_GENERATOR)
    message("Using external <generator> implementation")
    include(ExternalProject)
    ExternalProject_Add(
            generator
            PREFIX ${CMAKE_SOURCE_DIR}/generator
            GIT_REPOSITORY https://github.com/todoubaba/generator
            GIT_TAG a849a206f35c2447ab5e605edc5fcf44f673c628 # no release
            INSTALL_COMMAND ""
            BUILD_COMMAND ""
)
endif (GCS_COMPILER_HAS_GENERATOR)

try_compile(GCS_COMPILER_HAS_STACKTRACE ${CMAKE_BINARY_DIR}/cmake_compile_tests ${CMAKE_SOURCE_DIR}/cmake_compile_tests/has_stacktrace.cc)
if (GCS_COMPILER_HAS_STACKTRACE)
    message("Using compiler's own <stacktrace> implementation")
else (GCS_COMPILER_HAS_STACKTRACE)
    message("No <stacktrace> implementation available")
endif (GCS_COMPILER_HAS_STACKTRACE)

include_directories(.)
add_subdirectory(gcs)

if (GCS_ENABLE_EXAMPLES)
    add_subdirectory(examples)
    add_subdirectory(minicp_benchmarks)
    add_subdirectory(test)
endif (GCS_ENABLE_EXAMPLES)

if (GCS_ENABLE_DOXYGEN)
    find_package(Doxygen)

    if (DOXYGEN_FOUND)
        # set input and output files
        set(DOXYGEN_IN ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in)
        set(DOXYGEN_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)

        # request to configure the file
        configure_file(${DOXYGEN_IN} ${DOXYGEN_OUT} @ONLY)
        add_custom_target(docs
                COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYGEN_OUT}
                WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
                VERBATIM)
    else (DOXYGEN_FOUND)
        message("Could not find Doxygen to generate documentation")
    endif (DOXYGEN_FOUND)
endif (GCS_ENABLE_DOXYGEN)

if (GCS_ENABLE_XCSP)
    add_subdirectory(xcsp)
endif (GCS_ENABLE_XCSP)

if (GCS_ENABLE_MINIZINC)
    add_subdirectory(minizinc)
endif (GCS_ENABLE_MINIZINC)

if (GCS_ENABLE_PYTHON)
    add_subdirectory(python)
endif (GCS_ENABLE_PYTHON)

Include(FetchContent)
Set(FETCHCONTENT_QUIET FALSE)

FetchContent_Declare(
        Catch2
        GIT_REPOSITORY https://github.com/catchorg/Catch2.git
        GIT_TAG b670de4fe12ac7c5e858b7de3a14fb4bd18c760e # v3.4.10
)
FetchContent_MakeAvailable(Catch2)

FetchContent_Declare(
        cxxopts
        GIT_REPOSITORY https://github.com/jarro2783/cxxopts.git
        GIT_TAG 44380e5a44706ab7347f400698c703eb2a196202 # v3.3.1
)
FetchContent_MakeAvailable(cxxopts)

try_compile(GCS_COMPILER_HAS_FORMAT ${CMAKE_BINARY_DIR}/cmake_compile_tests ${CMAKE_SOURCE_DIR}/cmake_compile_tests/has_format.cc)
if (GCS_COMPILER_HAS_FORMAT)
    message("Using compiler's own <format> and <print> implementation")
else (GCS_COMPILER_HAS_FORMAT)
    message("Using libfmt instead of <format> and <print>")
    FetchContent_Declare(
            fmt
            GIT_REPOSITORY https://github.com/fmtlib/fmt.git
            GIT_TAG 40626af88bd7df9a5fb80be7b25ac85b122d6c21 # v11.2.0
    )
    FetchContent_MakeAvailable(fmt)
    target_link_libraries(gcs_fmt INTERFACE fmt::fmt)
endif (GCS_COMPILER_HAS_FORMAT)

set(JSON_BuildTests OFF CACHE INTERNAL "")
FetchContent_Declare(
        json
        GIT_REPOSITORY https://github.com/nlohmann/json.git
        GIT_TAG 9cca280a4d0ccf0c08f47a99aa71d1b0e52f8d03 # v3.11.3
)
FetchContent_MakeAvailable(json)
