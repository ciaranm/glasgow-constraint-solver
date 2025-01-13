add_executable(n_fractions n_fractions.cc)
target_link_libraries(n_fractions PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(n_fractions LINK_PUBLIC ${Boost_LIBRARIES})
