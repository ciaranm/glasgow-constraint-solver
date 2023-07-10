add_executable(smart_table_lex smart_table_lex.cc)
target_link_libraries(smart_table_lex PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(smart_table_lex LINK_PUBLIC ${Boost_LIBRARIES})