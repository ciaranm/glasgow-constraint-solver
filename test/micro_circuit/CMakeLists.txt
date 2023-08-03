add_executable(micro_circuit micro_circuit.cc)
target_link_libraries(micro_circuit PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(micro_circuit LINK_PUBLIC ${Boost_LIBRARIES})