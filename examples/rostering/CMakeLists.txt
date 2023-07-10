add_executable(rostering rostering.cc)
target_link_libraries(rostering PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(rostering LINK_PUBLIC ${Boost_LIBRARIES})