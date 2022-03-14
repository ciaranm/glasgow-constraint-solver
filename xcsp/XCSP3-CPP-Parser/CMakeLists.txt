cmake_minimum_required(VERSION 3.6)

project("xcsp3parser")

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/samples")
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/lib")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/lib)

set(CMAKE_CXX_STANDARD 11)

set(Xcsp3Parser_VERSION_MAJOR 1)
set(Xcsp3Parser_VERSION_MINOR 0)
set(Xcsp3Parser_VERSION_PATCH 0)
set(VERSION ${Xcsp3Parser_VERSION_MAJOR}.${Xcsp3Parser_VERSION_MINOR}.${Xcsp3Parser_VERSION_PATCH})

#configure_file(
#        "${PROJECT_SOURCE_DIR}/include/Xcsp3ParserConfig.h.in"
#        "${PROJECT_BINARY_DIR}/include/Xcsp3ParserConfig.h"
#)
find_package(LibXml2 REQUIRED)
include_directories(${LIBXML2_INCLUDE_DIR})

set(LIBRARY_NAME xcsp3parser)

set(LIB_HEADERS
        include/AttributeList.h
        include/UTF8String.h
        include/XCSP3Constants.h
        include/XCSP3Constraint.h
        include/XCSP3CoreParser.h
        include/XCSP3CoreCallbacks.h
        include/XCSP3Manager.h
        include/XCSP3Domain.h
        include/XCSP3Objective.h
        include/XCSP3utils.h
        include/XCSP3Variable.h
        include/XMLParser.h
        include/XCSP3Tree.h
        include/XCSP3TreeNode.h
        )

set(LIB_SOURCES
        src/UTF8String.cc
        src/XCSP3Code.cc
        src/XCSP3CoreParser.cc
        src/XCSP3Manager.cc
        src/XMLParser.cc
        src/XMLParserTags.cc
        src/XCSP3Tree.cc
        src/XCSP3TreeNode.cc
        )

set(APP_HEADERS
        )

set(APP_SOURCES
        samples/XCSP3PrintCallbacks.h
        samples/main.cc
        include/XCSP3TreeNode.h)

include_directories(
        ${PROJECT_SOURCE_DIR}/include
)

add_library(${LIBRARY_NAME} STATIC ${LIB_SOURCES} ${LIB_HEADERS})
#add_library(${LIBRARY_NAME} SHARED ${LIB_SOURCES} ${LIB_HEADERS})
target_link_libraries(${LIBRARY_NAME} ${LIBXML2_LIBRARIES})

set_target_properties(${LIBRARY_NAME} PROPERTIES
        VERSION ${VERSION}
        FRAMEWORK FALSE
        PUBLIC_HEADER "${LIB_HEADERS}" # specify the public headers
        )

set(APPLICATION_NAME samplesXcsp3)
add_executable(${APPLICATION_NAME} ${APP_SOURCES})
target_link_libraries(${APPLICATION_NAME} ${LIBRARY_NAME} ${LIBXML2_LIBRARIES})
target_include_directories(${LIBRARY_NAME} PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/include)


