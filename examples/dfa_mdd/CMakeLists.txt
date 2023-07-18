add_executable(dfa_mdd dfa_mdd.cc)
target_link_libraries(dfa_mdd PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(dfa_mdd LINK_PUBLIC ${Boost_LIBRARIES})