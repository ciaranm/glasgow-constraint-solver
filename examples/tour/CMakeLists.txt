add_executable(tour tour.cc)
target_link_libraries(tour PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(tour LINK_PUBLIC ${Boost_LIBRARIES})
