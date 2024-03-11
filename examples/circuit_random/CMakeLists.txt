add_executable(circuit_random circuit_random.cc)
target_link_libraries(circuit_random PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(circuit_random LINK_PUBLIC ${Boost_LIBRARIES})