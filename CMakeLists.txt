cmake_minimum_required(VERSION 3.18)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

add_compile_options(-W)
add_compile_options(-Wall)
add_compile_options(-O3)
add_compile_options(-march=native)
add_compile_options(-g)
add_compile_options(-g3)
add_compile_options(-pthread)
add_link_options(-pthread)

# add_compile_options(-DGCS_TRACK_ALL_PROPAGATIONS=1)

project(
    Glasgow-Constraint-Solver
    VERSION 0.0.1
    DESCRIPTION "An auditable constraint programming and optimisation solver"
    HOMEPAGE_URL "https://github.com/ciaranm/glasgow-constraint-solver"
    LANGUAGES CXX)

enable_testing()

option(GCS_ENABLE_DOXYGEN "Add a doxygen target to generate the documentation" OFF)
option(GCS_ENABLE_XCSP "Support for the XCSP modelling language" ON)
option(GCS_ENABLE_EXAMPLES "Build examples" ON)

include_directories(.)
add_subdirectory(gcs)

if (GCS_ENABLE_EXAMPLES)
    add_subdirectory(examples)
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
  GIT_TAG        97c48e0c343d26d50764fafdc90b1e630fbd10ce # v3.1.0
)
FetchContent_MakeAvailable(Catch2)

SET(CATCH_CONFIG_ENABLE_ALL_STRINGMAKERS ON)
