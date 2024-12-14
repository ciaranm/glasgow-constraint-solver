add_executable(single_mult single_mult.cc)
target_link_libraries(single_mult PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(single_mult LINK_PUBLIC ${Boost_LIBRARIES})