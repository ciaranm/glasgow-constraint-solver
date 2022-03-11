add_executable(magic_square magic_square.cc)
target_link_libraries(magic_square PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(magic_square LINK_PUBLIC ${Boost_LIBRARIES})
