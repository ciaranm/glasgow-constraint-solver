add_executable(disconnected disconnected.cc)
target_link_libraries(disconnected PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(disconnected LINK_PUBLIC ${Boost_LIBRARIES})