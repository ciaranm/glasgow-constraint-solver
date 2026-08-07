add_executable(seat_moving seat_moving.cc)
target_link_libraries(seat_moving PRIVATE glasgow_constraint_solver)
target_link_libraries(seat_moving PRIVATE cxxopts)

# The default instance is deliberately tiny. The MiniZinc Challenge instances
# the binary also carries are what the proof benchmark set reaches for; the
# reference one, sm-10-12-00, writes a 645MB proof and is nowhere near a ctest.
add_test(NAME seat_moving COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename seat_moving $<TARGET_FILE:seat_moving>)
add_test(NAME seat_moving-not-equals COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename seat_moving-not-equals $<TARGET_FILE:seat_moving> --all-different not-equals)
add_test(NAME seat_moving-vc COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename seat_moving-vc $<TARGET_FILE:seat_moving> --all-different vc)
add_test(NAME seat_moving-random COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename seat_moving-random $<TARGET_FILE:seat_moving> --seats 7 --people 4 --seed 1)

# The .dzn reader, on the built-in `small` instance written out as data, so this
# lane and `--instance small` must reach the same answer. It is also the only
# lane anywhere that reads a Boolean array, which is what Can_swap is. Nothing
# else in examples/ runs this reader: before issue #664 moved it onto the shared
# examples/dzn.hh it was reachable only by hand, with a Challenge data file that
# is not in the tree.
add_test(NAME seat_moving-dzn COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename seat_moving-dzn
    $<TARGET_FILE:seat_moving> --dzn ${CMAKE_CURRENT_SOURCE_DIR}/sample.dzn)

# The proof lane above says the reader produced a model that solves and whose
# proof checks out; it cannot say the reader read the right numbers, because a
# proof of a differently-parsed instance verifies just as happily. So a second,
# proofless lane pins the answer, which is what a misparse changes.
add_test(NAME seat_moving-dzn-answer COMMAND $<TARGET_FILE:seat_moving> --dzn ${CMAKE_CURRENT_SOURCE_DIR}/sample.dzn)
set_tests_properties(seat_moving-dzn-answer PROPERTIES PASS_REGULAR_EXPRESSION "objective = 40")
