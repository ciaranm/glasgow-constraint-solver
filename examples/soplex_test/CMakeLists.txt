add_executable(soplex_test soplex_test.cc)
target_link_libraries(soplex_test PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(soplex_test LINK_PUBLIC ${Boost_LIBRARIES})
target_link_libraries(soplex_test LINK_PUBLIC libsoplex)