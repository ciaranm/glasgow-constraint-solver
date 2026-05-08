include(FetchContent)

FetchContent_Declare(xcsp3_cpp_parser
    GIT_REPOSITORY https://github.com/xcsp3team/XCSP3-CPP-Parser.git
    GIT_TAG 179670dd97cd2b87cdeb93aa7268b57bba719490
    EXCLUDE_FROM_ALL)
FetchContent_MakeAvailable(xcsp3_cpp_parser)

find_package(LibXml2 REQUIRED)

add_executable(xcsp_glasgow_constraint_solver xcsp_glasgow_constraint_solver.cc)
target_link_libraries(xcsp_glasgow_constraint_solver PRIVATE
    xcsp3parser
    LibXml2::LibXml2
    glasgow_constraint_solver
    cxxopts)

add_test(NAME xcsp_sum_not_equals COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ sum_not_equals "^d FOUND SOLUTIONS 8$")
set_tests_properties(xcsp_sum_not_equals PROPERTIES RESOURCE_LOCK xcsp)

add_test(NAME xcsp_intension_basic COMMAND ${CMAKE_SOURCE_DIR}/xcsp/run_xcsp_test.bash $<TARGET_FILE:xcsp_glasgow_constraint_solver> ${CMAKE_SOURCE_DIR}/xcsp/tests/ intension_basic "^d FOUND SOLUTIONS 5$")
set_tests_properties(xcsp_intension_basic PROPERTIES RESOURCE_LOCK xcsp)
