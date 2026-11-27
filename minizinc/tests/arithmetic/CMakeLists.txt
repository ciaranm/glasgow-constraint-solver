gcs_minizinc_test(minizinc-abs abs.mzn true true)

gcs_minizinc_test(minizinc-arrayintminmax array_min_max.mzn false true)

gcs_minizinc_test(minizinc-div div.mzn true true)

gcs_minizinc_test(minizinc-minmax min_max.mzn false true)

gcs_minizinc_test(minizinc-times times.mzn true true)

# The shapes a front end hands the arithmetic builtins (#1006), several to a
# model, each guarded by a count so that one shape folded away by the flattener
# cannot hide behind the others. The counts are quoted, so that int_div does not
# also count, say, a future int_div_reif. --reference-std adds the standard
# library's reading wherever Gecode on it can run the model, since Gecode's own
# arithmetic is native and agreeing with both is different evidence.
#
# Division and modulus: negative operands, constants on either side, a variable
# divided by itself, and a divisor whose domain includes 0. In a root context the
# flattener punches 0 out of the divisor's domain, so it reaches us as a domain
# with a hole; under a reification it must make the comparison false instead.
gcs_minizinc_test(minizinc-arithmetic-div-mod-shapes div_mod_shapes.mzn true true
    OPTIONS --fzn-count 4 "\"int_div\"" --fzn-count 4 "\"int_mod\"" --reference-std)

gcs_minizinc_test(minizinc-arithmetic-div-mod-reif div_mod_reif.mzn true true
    OPTIONS --fzn-count 1 "\"int_div\"" --fzn-count 1 "\"int_mod\"" --reference-std)

# Power with a variable exponent, the only way to reach int_pow: zero and
# negative exponents and bases, where MiniZinc's 1 div x ^ |y| reading applies.
# These compare against MiniZinc's default solver only: the standard library has
# no decomposition of int_pow, so Gecode under -G std stops with
# `Registry: Constraint int_pow not found`.
gcs_minizinc_test(minizinc-arithmetic-pow-shapes pow_shapes.mzn true true
    OPTIONS --fzn-count 3 "\"int_pow\"")

gcs_minizinc_test(minizinc-arithmetic-pow-reif pow_reif.mzn true true
    OPTIONS --fzn-count 1 "\"int_pow\"")

# Multiplication with negative and zero factors and a square, which hands the
# builtin the same variable twice.
gcs_minizinc_test(minizinc-arithmetic-times-shapes times_shapes.mzn true true
    OPTIONS --fzn-count 5 "\"int_times\"" --reference-std)

# Absolute value over domains straddling zero, with holes, wholly negative, and
# a variable equal to its own absolute value.
gcs_minizinc_test(minizinc-arithmetic-abs-shapes abs_shapes.mzn true true
    OPTIONS --fzn-count 4 "\"int_abs\"" --reference-std)

# Binary min and max with constants, a repeated variable and a result that is
# one of the operands.
gcs_minizinc_test(minizinc-arithmetic-min-max-shapes min_max_shapes.mzn true true
    OPTIONS --fzn-count 3 "\"int_min\"" --fzn-count 3 "\"int_max\"" --reference-std)

# Array min and max with constants among the variables, a repeated variable and
# arrays not indexed from 1. The two builtins reach Glasgow only because
# mznlib/redefinitions-2.0.mzn replaces the standard library's file of that
# name, which decomposes them into chains of int_min and int_max; the solutions
# agree either way, so only the counts would notice that file going.
gcs_minizinc_test(minizinc-arithmetic-array-min-max-shapes array_min_max_shapes.mzn true true
    OPTIONS --fzn-count 2 "\"array_int_minimum\"" --fzn-count 2 "\"array_int_maximum\"" --reference-std)
