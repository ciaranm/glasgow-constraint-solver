add_executable(random_regular random_regular.cc)
target_link_libraries(random_regular PUBLIC glasgow_constraint_solver)

add_test(NAME random_regular COMMAND $<TARGET_FILE:random_regular>)