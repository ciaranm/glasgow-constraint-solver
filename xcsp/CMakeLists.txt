include(ExternalProject)
ExternalProject_Add(XCSP3-CPP-Parser
    PREFIX ${CMAKE_SOURCE_DIR}/XCSP3-CPP-Parser
    GIT_REPOSITORY https://github.com/xcsp3team/XCSP3-CPP-Parser.git
    GIT_TAG c1a12b0a850a294d2065018d0bfa2fc9404fc30f
    INSTALL_COMMAND "")

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
add_executable(xcsp_glasgow_constraint_solver xcsp_glasgow_constraint_solver.cc)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})

find_package(LibXml2 REQUIRED)
include_directories(${LIBXML2_INCLUDE_DIR})

target_link_libraries(xcsp_glasgow_constraint_solver
    PUBLIC
    ${CMAKE_SOURCE_DIR}/XCSP3-CPP-Parser/src/XCSP3-CPP-Parser/lib/libxcsp3parser.a
    glasgow_constraint_solver
    ${Boost_LIBRARIES}
    ${LIBXML2_LIBRARIES})

include_directories(${CMAKE_SOURCE_DIR}/XCSP3-CPP-Parser/src/XCSP3-CPP-Parser/include/)

add_test(NAME xcsp_sum_not_equals COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ sum_not_equals "^d FOUND SOLUTIONS 8$")
set_tests_properties(xcsp_sum_not_equals PROPERTIES RESOURCE_LOCK xcsp)
