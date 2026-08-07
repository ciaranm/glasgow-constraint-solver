add_executable(nonogram nonogram.cc)
target_link_libraries(nonogram PRIVATE glasgow_constraint_solver)
target_link_libraries(nonogram PRIVATE cxxopts)

add_test(NAME nonogram COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename nonogram $<TARGET_FILE:nonogram>)
add_test(NAME nonogram-all COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename nonogram-all $<TARGET_FILE:nonogram> --all)
add_test(NAME nonogram-bacchus COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename nonogram-bacchus $<TARGET_FILE:nonogram> --bacchus)
add_test(NAME nonogram-legacy COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename nonogram-legacy $<TARGET_FILE:nonogram> --legacy)
add_test(NAME nonogram-heart COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename nonogram-heart $<TARGET_FILE:nonogram> --puzzle heart)

# The .dzn reader, on the built-in `plus` puzzle written in the Challenge 2013
# padded-cons format, so this lane and `--puzzle plus` must draw the same
# picture. Nothing else in examples/ runs this reader: before issue #664 moved
# it onto the shared examples/dzn.hh it was reachable only by hand, with a
# Challenge data file that is not in the tree.
add_test(NAME nonogram-dzn COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename nonogram-dzn
    $<TARGET_FILE:nonogram> --dzn ${CMAKE_CURRENT_SOURCE_DIR}/sample.dzn)

# The proof lane above says the reader produced a model that solves and whose
# proof checks out; it cannot say the reader read the right numbers, because a
# proof of a differently-parsed instance verifies just as happily. So a second,
# proofless lane pins the answer, which is what a misparse changes.
add_test(NAME nonogram-dzn-answer COMMAND $<TARGET_FILE:nonogram> --dzn ${CMAKE_CURRENT_SOURCE_DIR}/sample.dzn)
set_tests_properties(nonogram-dzn-answer PROPERTIES PASS_REGULAR_EXPRESSION "#####")
