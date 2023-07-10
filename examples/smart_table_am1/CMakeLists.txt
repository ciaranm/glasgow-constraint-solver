add_executable(smart_table_am1 smart_table_am1.cc)
target_link_libraries(smart_table_am1 PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(smart_table_am1 LINK_PUBLIC ${Boost_LIBRARIES})