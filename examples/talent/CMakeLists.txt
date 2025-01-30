add_executable(talent talent.cc)
target_link_libraries(talent PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(talent LINK_PUBLIC ${Boost_LIBRARIES})