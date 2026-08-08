add_executable(hitori hitori.cc)
target_link_libraries(hitori PRIVATE glasgow_constraint_solver)
target_link_libraries(hitori PRIVATE cxxopts)

add_test(NAME hitori COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename hitori $<TARGET_FILE:hitori>)
add_test(NAME hitori-no-connectivity COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename hitori-no-connectivity $<TARGET_FILE:hitori> --connectivity none)

# The .dzn reader, on the same grid `--size 4 --seed 0` generates, so this lane
# and the generator must agree on the optimum. Nothing else in examples/ runs
# this reader: before issue #664 moved it onto the shared examples/dzn.hh it was
# reachable only by hand, with a Challenge data file that is not in the tree.
add_test(NAME hitori-dzn COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename hitori-dzn
    $<TARGET_FILE:hitori> --dzn ${CMAKE_CURRENT_SOURCE_DIR}/sample.dzn)

# The proof lane above says the reader produced a model that solves and whose
# proof checks out; it cannot say the reader read the right numbers, because a
# proof of a differently-parsed instance verifies just as happily. So a second,
# proofless lane pins the answer, which is what a misparse changes.
add_test(NAME hitori-dzn-answer COMMAND $<TARGET_FILE:hitori> --dzn ${CMAKE_CURRENT_SOURCE_DIR}/sample.dzn)
set_tests_properties(hitori-dzn-answer PROPERTIES PASS_REGULAR_EXPRESSION "obj = 13")
