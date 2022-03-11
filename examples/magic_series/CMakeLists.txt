add_executable(magic_series magic_series.cc)
target_link_libraries(magic_series PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(magic_series LINK_PUBLIC ${Boost_LIBRARIES})
