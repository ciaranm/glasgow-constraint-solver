add_executable(highs_test highs_test.cc)
target_link_libraries(highs_test PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(highs_test LINK_PUBLIC ${Boost_LIBRARIES})
target_link_libraries(highs_test LINK_PUBLIC highs)