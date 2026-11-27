gcs_minizinc_test(minizinc-aust aust.mzn true true)

gcs_minizinc_test(minizinc-cake cake.mzn false true)

gcs_minizinc_test(minizinc-crystalmaze crystal_maze.mzn true true)

gcs_minizinc_test(minizinc-nurses nurses.mzn true false)

gcs_minizinc_test(minizinc-small small.mzn true true)

gcs_minizinc_test(minizinc-tsp tsp.mzn false true)

# Classic small puzzles with known solution counts (#1006), for variety rather
# than for any one shape: SEND + MORE = MONEY (one solution), six queens (four),
# the 3 x 3 magic square (eight), Langford's L(2, 4) (two), the five-mark Golomb
# ruler (length 11) and the three-digit Armstrong numbers (four). The counts pin
# that the globals each one leans on reached their builtins.
gcs_minizinc_test(minizinc-models-send-more-money send_more_money.mzn true true
    OPTIONS --fzn-count 1 glasgow_alldifferent --reference-std)

gcs_minizinc_test(minizinc-models-queens queens.mzn true true
    OPTIONS --fzn-count 3 glasgow_alldifferent --reference-std)

gcs_minizinc_test(minizinc-models-magic-square magic_square.mzn true true
    OPTIONS --fzn-count 1 glasgow_alldifferent --fzn-count 8 "\"int_lin_eq\"" --reference-std)

gcs_minizinc_test(minizinc-models-langford langford.mzn true true
    OPTIONS --fzn-count 1 glasgow_alldifferent --fzn-count 4 "\"int_lin_eq\"" --reference-std)

gcs_minizinc_test(minizinc-models-golomb golomb.mzn false true
    OPTIONS --fzn-count 1 glasgow_alldifferent --fzn-count 1 glasgow_strictly_increasing_int --reference-std)

# Armstrong numbers run without proofs: the cubes multiply digits into
# products up to 729 and n ranges over 100..999, and Multiply's proof logging
# over those widths writes an 800 MB proof that takes VeriPB 50 seconds, for four
# solutions. arithmetic/ has the proof-checked lanes for the same builtins.
gcs_minizinc_test(minizinc-models-armstrong armstrong.mzn true false
    OPTIONS --fzn-count 2 "\"int_div\"" --fzn-count 2 "\"int_mod\"" --fzn-count 6 "\"int_times\"" --reference-std)
