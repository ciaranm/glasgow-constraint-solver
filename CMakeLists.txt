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
option(GCS_ENABLE_EXAMPLES "Build examples" ON)
option(GCS_DEBUG_MODE "Disable compiler optimisation for debugging" OFF)

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

Include(FetchContent)
Set(FETCHCONTENT_QUIET FALSE)
FetchContent_Declare(
        Catch2
        GIT_REPOSITORY https://github.com/catchorg/Catch2.git
        GIT_TAG 65cc7fd2ae39a7a543767f661b096d7d521ee4f0 # v3.2.0
)
FetchContent_MakeAvailable(Catch2)

SET(CATCH_CONFIG_ENABLE_ALL_STRINGMAKERS ON)
