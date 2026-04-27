include(ExternalProject)
ExternalProject_Add(XCSP3-CPP-Parser
    PREFIX ${CMAKE_SOURCE_DIR}/XCSP3-CPP-Parser
    GIT_REPOSITORY https://github.com/xcsp3team/XCSP3-CPP-Parser.git
    GIT_TAG 807f475c5b705d085215de61b811c1fbf0152398
    INSTALL_COMMAND "")

add_executable(xcsp_glasgow_constraint_solver xcsp_glasgow_constraint_solver.cc)
target_include_directories(xcsp_glasgow_constraint_solver PRIVATE
    ${CMAKE_SOURCE_DIR}/XCSP3-CPP-Parser/src/XCSP3-CPP-Parser/include/)

find_package(LibXml2 REQUIRED)

target_link_libraries(xcsp_glasgow_constraint_solver PRIVATE
    ${CMAKE_SOURCE_DIR}/XCSP3-CPP-Parser/src/XCSP3-CPP-Parser/lib/libxcsp3parser.a
    glasgow_constraint_solver
    cxxopts
    LibXml2::LibXml2)

add_test(NAME xcsp_sum_not_equals COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ sum_not_equals "^d FOUND SOLUTIONS 8$")
set_tests_properties(xcsp_sum_not_equals PROPERTIES RESOURCE_LOCK xcsp)
