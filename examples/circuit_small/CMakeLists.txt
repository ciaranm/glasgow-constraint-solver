add_executable(circuit_small circuit_small.cc)
target_link_libraries(circuit_small PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(circuit_small LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME circuit_small COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:circuit_small>)
