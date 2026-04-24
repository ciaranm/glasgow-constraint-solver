add_executable(tables tables.cc)
target_link_libraries(tables PUBLIC glasgow_constraint_solver)


target_link_libraries(tables LINK_PUBLIC cxxopts)
target_link_libraries(tables PRIVATE fmt::fmt)

add_test(NAME tables COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:tables>)

