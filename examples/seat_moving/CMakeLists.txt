add_executable(seat_moving seat_moving.cc)
target_link_libraries(seat_moving PRIVATE glasgow_constraint_solver)
target_link_libraries(seat_moving PRIVATE cxxopts)

# The default instance is deliberately tiny. The MiniZinc Challenge instances
# the binary also carries are what the proof benchmark set reaches for; the
# reference one, sm-10-12-00, writes a 645MB proof and is nowhere near a ctest.
add_test(NAME seat_moving COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename seat_moving $<TARGET_FILE:seat_moving>)
add_test(NAME seat_moving-not-equals COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename seat_moving-not-equals $<TARGET_FILE:seat_moving> --all-different not-equals)
add_test(NAME seat_moving-random COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename seat_moving-random $<TARGET_FILE:seat_moving> --seats 7 --people 4 --seed 1)
