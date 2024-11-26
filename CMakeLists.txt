cmake_minimum_required(VERSION 3.18)
set(CMAKE_CXX_STANDARD 20)
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

unset(COMPILER_SUPPORTS_NO_ANNOYING_WARNINGS_ABOUT_MOVE CACHE)
CHECK_CXX_COMPILER_FLAG(-Wno-unqualified-std-cast-call COMPILER_SUPPORTS_NO_ANNOYING_WARNINGS_ABOUT_MOVE)
if (COMPILER_SUPPORTS_NO_ANNOYING_WARNINGS_ABOUT_MOVE)
    add_compile_options(-Wno-unqualified-std-cast-call)
endif (COMPILER_SUPPORTS_NO_ANNOYING_WARNINGS_ABOUT_MOVE)

add_compile_options(-g)
add_compile_options(-g3)
add_compile_options(-gdwarf-3)
add_compile_options(-pthread)

add_link_options(-pthread)

if (NOT GCS_DEBUG_MODE)
    add_compile_options(-O3)
endif (NOT GCS_DEBUG_MODE)

# add_compile_options(-DGCS_TRACK_ALL_PROPAGATIONS=1)

enable_testing()

option(GCS_ENABLE_DOXYGEN "Add a doxygen target to generate the documentation" OFF)
option(GCS_ENABLE_XCSP "Support for the XCSP modelling language" ON)
option(GCS_ENABLE_MINIZINC "Support for the MiniZinc modelling language" ON)
option(GCS_ENABLE_EXAMPLES "Build examples" ON)
option(GCS_DEBUG_MODE "Disable compiler optimisation for debugging" OFF)
option(GCS_ENABLE_SOPLEX "(Experimental) Required for WIP LP justifications." ON)
option(GCS_ENABLE_HIGHS "(Experimental) Required for WIP LP justifications." ON)

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
        GIT_TAG 6e79e682b726f524310d55dec8ddac4e9c52fb5f # v3.4.0
)
FetchContent_MakeAvailable(Catch2)
SET(CATCH_CONFIG_ENABLE_ALL_STRINGMAKERS ON)

FetchContent_Declare(
        fmt
        GIT_REPOSITORY https://github.com/fmtlib/fmt.git
        GIT_TAG e69e5f977d458f2650bb346dadf2ad30c5320281 # v10.2.1
)
FetchContent_MakeAvailable(fmt)

FetchContent_Declare(
        range-v3
        GIT_REPOSITORY https://github.com/ericniebler/range-v3.git
        GIT_TAG a81477931a8aa2ad025c6bda0609f38e09e4d7ec # v0.12.0
)
FetchContent_MakeAvailable(range-v3)

include(ExternalProject)
ExternalProject_Add(
        generator
        PREFIX ${CMAKE_SOURCE_DIR}/generator
        GIT_REPOSITORY https://github.com/todoubaba/generator
        GIT_TAG a849a206f35c2447ab5e605edc5fcf44f673c628 # no release
        INSTALL_COMMAND ""
        BUILD_COMMAND ""
)

if (GCS_ENABLE_MINIZINC)
    set(JSON_BuildTests OFF CACHE INTERNAL "")
    FetchContent_Declare(
            json
            GIT_REPOSITORY https://github.com/nlohmann/json.git
            GIT_TAG 9cca280a4d0ccf0c08f47a99aa71d1b0e52f8d03 # v3.11.3
    )
    FetchContent_MakeAvailable(json)
endif (GCS_ENABLE_MINIZINC)

if (GCS_ENABLE_SOPLEX)
    FetchContent_Declare(
            soplex
            GIT_REPOSITORY https://github.com/scipopt/soplex.git
            GIT_TAG release-712
    )
    block()
        set(CMAKE_CXX_STANDARD 17)
        set(CMAKE_CXX_STANDARD_REQUIRED ON)
        set(CMAKE_CXX_EXTENSIONS ON)
        FetchContent_MakeAvailable(soplex)
    endblock()
endif (GCS_ENABLE_SOPLEX)

if (GCS_ENABLE_HIGHS)
    FetchContent_Declare(
            HiGHS
            GIT_REPOSITORY https://github.com/ERGO-Code/HiGHS.git
            GIT_TAG v1.8.1
    )
    FetchContent_MakeAvailable(HiGHS)
endif (GCS_ENABLE_HIGHS)

