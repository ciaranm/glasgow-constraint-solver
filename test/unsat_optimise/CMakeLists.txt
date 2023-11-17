add_executable(unsat_optimise unsat_optimise.cc)
target_link_libraries(unsat_optimise PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(unsat_optimise LINK_PUBLIC ${Boost_LIBRARIES})