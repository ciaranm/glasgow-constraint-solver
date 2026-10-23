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

# With prune skip off the edges that skip a subtree stay in the domain, but the
# fix-required and no-back-edges certificates assume they are gone, so the
# propagator writes their derivations without pruning them (issue #1306). An edge
# into the root from a later subtree is pinned by circuit_prune_skip_off_test; this
# lane is pinned to an instance where an edge skipping a whole subtree is the one a
# later certificate needs: with that derivation left out, n=9 seed 69 is the only
# rejected proof among n=5..10, seeds 1..150. The graph comes from
# uniform_real_distribution, whose output the standard does not fix, so on another
# standard library this may be a different instance.
add_test(NAME circuit_random-no-prune-skip COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename circuit_random-no-prune-skip $<TARGET_FILE:circuit_random> --no-prune-skip -n 9 --seed 69)
