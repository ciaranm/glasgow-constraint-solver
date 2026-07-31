# Every program here is user-facing material AND a ctest: each is run with
# --prove and checked by VeriPB (see ../run_test_and_verify.bash). So examples/
# is load-bearing -- it is the project's end-to-end proof-logging regression
# suite, not just pedagogy, and a program added here needs a fixed instance
# whose proof verifies quickly.
#
# One exception: skeleton_puzzle is a genuine example, but has no add_test,
# because it does not finish in five minutes under --prove. Do not "fix" that by
# registering it -- it needs a smaller instance first.
#
# Programs that only measure something live in ../benchmarks/ instead, and the
# MiniCP comparison set in ../minicp_benchmarks/.
#
# Five of these are RNG stress-harnesses rather than examples to read
# (circuit_random, multiply_random, random_polynomial, regular_random,
# smart_table_random). Issue #292 proposed relocating them on the grounds that
# they were the only end-to-end proof check for their constraints. That is no
# longer true: 54 of the 59 constraint test files now verify their own proofs
# internally via can_run_veripb(), Multiply, Regular, SmartTable and Circuit
# among them. They are kept for now because they still exercise a random
# instance stream that the curated unit tests do not, but retiring them is now
# a judgement call rather than a coverage regression.
add_subdirectory(auto_table)
add_subdirectory(cake)
add_subdirectory(colour)
add_subdirectory(circuit_small)
add_subdirectory(circuit_random)
add_subdirectory(crystal_maze)
add_subdirectory(cumulative)
add_subdirectory(frequency_square)
add_subdirectory(knapsack)
add_subdirectory(langford)
add_subdirectory(money)
add_subdirectory(multiply_random)
add_subdirectory(n_fractions)
add_subdirectory(nonogram)
add_subdirectory(odd_even_sum)
add_subdirectory(p_dispersion)
add_subdirectory(ortho_latin)
add_subdirectory(regular_random)
add_subdirectory(random_polynomial)
add_subdirectory(regex)
add_subdirectory(rostering)
add_subdirectory(shikaku)
add_subdirectory(skeleton_puzzle)
add_subdirectory(skyscrapers)
add_subdirectory(smart_table_am1)
add_subdirectory(smart_table_lex)
add_subdirectory(smart_table_random)
add_subdirectory(smart_table_small)
add_subdirectory(sudoku)
add_subdirectory(table_layout)
add_subdirectory(tables)
add_subdirectory(tour)
add_subdirectory(tutorial_proof)
add_subdirectory(talent)
