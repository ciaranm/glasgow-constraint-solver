cmake_minimum_required(VERSION 3.18)
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

project(
    Glasgow-constraint-solver
    VERSION 0.0.1
    DESCRIPTION "An auditable constraint programming and optimisation solver"
    HOMEPAGE_URL "https://github.com/ciaranm/glasgow-constraint-solver"
    LANGUAGES CXX)

include_directories(.)
add_subdirectory(gcs)
add_subdirectory(examples)

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
