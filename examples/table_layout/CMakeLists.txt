add_executable(table_layout table_layout.cc)
target_link_libraries(table_layout PRIVATE glasgow_constraint_solver)


target_link_libraries(table_layout PRIVATE cxxopts)

add_test(NAME table_layout-table COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename table_layout-table $<TARGET_FILE:table_layout> --variant table)
add_test(NAME table_layout-auto-table COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename table_layout-auto-table $<TARGET_FILE:table_layout> --variant auto-table)
add_test(NAME table_layout-element COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename table_layout-element $<TARGET_FILE:table_layout> --variant element)

# The .dzn reader, on a hand-written instance carrying both the things a
# generated one does not: the array3d(...) wrapper the Challenge data uses, and
# cells with fewer configurations than maxconfig, so the negative padding is
# there to be mistaken for a configuration. Nothing else in examples/ runs this
# reader: before issue #664 moved it onto the shared examples/dzn.hh it was
# reachable only by hand, with a Challenge data file that is not in the tree.
add_test(NAME table_layout-dzn COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename table_layout-dzn
    $<TARGET_FILE:table_layout> --dzn ${CMAKE_CURRENT_SOURCE_DIR}/sample.dzn)

# The proof lane above says the reader produced a model that solves and whose
# proof checks out; it cannot say the reader read the right numbers, because a
# proof of a differently-parsed instance verifies just as happily. So a second,
# proofless lane pins the answer, which is what a misparse changes.
add_test(NAME table_layout-dzn-answer COMMAND $<TARGET_FILE:table_layout> --dzn ${CMAKE_CURRENT_SOURCE_DIR}/sample.dzn)
set_tests_properties(table_layout-dzn-answer PROPERTIES PASS_REGULAR_EXPRESSION "totalheight: 7")
