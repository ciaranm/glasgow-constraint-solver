add_executable(circuit_random circuit_random.cc)
target_link_libraries(circuit_random PRIVATE glasgow_constraint_solver)

target_link_libraries(circuit_random PRIVATE cxxopts)

# Circuit's all-different comes in two flavours, and until issue #642 only one of
# them was ever run: by default Circuit writes the clique-of-not-equals encoding
# itself, and under --gac-all-different a child AllDifferent writes it instead and
# adds a GAC propagator. The two OPBs are meant to be identical, so what the second
# lane buys is the other half of prepare()/define_proof_model() plus the GAC
# propagator's own justifications appearing inside a Circuit proof.
#
# That last part only happens if GAC actually prunes something, which it does not at
# the default n=3, so this lane is pinned to an instance where it does: n=6 seed 1
# takes 11 recursions with the option on against 15 with it off.
add_test(NAME circuit_random COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename circuit_random $<TARGET_FILE:circuit_random>)
add_test(NAME circuit_random-gac-all-different COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename circuit_random-gac-all-different $<TARGET_FILE:circuit_random> --gac-all-different -n 6 --seed 1)
