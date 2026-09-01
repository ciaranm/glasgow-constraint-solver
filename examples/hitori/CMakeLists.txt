add_executable(hitori hitori.cc)
target_link_libraries(hitori PRIVATE glasgow_constraint_solver)
target_link_libraries(hitori PRIVATE cxxopts)

add_test(NAME hitori COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename hitori $<TARGET_FILE:hitori>)
add_test(NAME hitori-no-connectivity COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename hitori-no-connectivity $<TARGET_FILE:hitori> --connectivity none)

# The native `Reachable` propagator, with its cut-vertex and bridge forcing on
# (the default) and off. These are the settings dev_docs/connectivity-proofs.md
# measures, and the only place in the tree where the propagator meets an
# instance-sized graph with an existentially quantified root, which is what
# makes the forcing pay a proof line per candidate root. Both are cheaper to
# solve and to check than the decomposition lane above, so this is coverage
# rather than a cost trade.
add_test(NAME hitori-propagator COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename hitori-propagator $<TARGET_FILE:hitori> --connectivity propagator)
add_test(NAME hitori-propagator-no-cuts COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename hitori-propagator-no-cuts $<TARGET_FILE:hitori> --connectivity propagator-no-cuts)

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
