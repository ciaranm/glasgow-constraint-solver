add_executable(synthetic_among synthetic_among.cc)
target_link_libraries(synthetic_among PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(synthetic_among LINK_PUBLIC ${Boost_LIBRARIES})