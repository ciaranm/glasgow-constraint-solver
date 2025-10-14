add_executable(smart_table_experiments smart_table_experiments.cc)
target_link_libraries(smart_table_experiments PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(smart_table_experiments LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME smart_table_experiments COMMAND $<TARGET_FILE:smart_table_experiments>)