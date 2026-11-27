gcs_minizinc_test(minizinc-arrayint array_int.mzn true true)

gcs_minizinc_test(minizinc-arrayvar array_var.mzn true true)

gcs_minizinc_test(minizinc-equals equals.mzn false true)

# Arrays not indexed from 1 (#1006). FlatZinc arrays are 1-based, so MiniZinc
# shifts the index into a fresh variable defined by a two-term int_lin_eq,
# which fzn-glasgow posts as an equality with an offset view, and then
# array_*_element applies its own offset of 1. The models cover parameter
# arrays indexed from 0, from a negative value and from 1000; arrays of
# variables with the result aliased with the index or with an entry of the
# array (on a 1-based array the builtin gets one variable as both index and
# result); Boolean arrays of both kinds, at the top level and inside a Boolean
# expression; and reified and half-reified calls whose index can fall outside
# the array. Each index variable's domain reaches past its array. --fzn-count
# insists that every element reached the builtin.
gcs_minizinc_test(minizinc-element-par par_shapes.mzn true true
    OPTIONS --fzn-count 3 array_int_element --reference-std)

gcs_minizinc_test(minizinc-element-var var_shapes.mzn true true
    OPTIONS --fzn-count 3 array_var_int_element --reference-std)

gcs_minizinc_test(minizinc-element-bool bool_shapes.mzn true true
    OPTIONS --fzn-count 2 array_bool_element
            --fzn-count 1 array_var_bool_element --reference-std)

gcs_minizinc_test(minizinc-element-partial partial.mzn true true
    OPTIONS --fzn-count 1 array_int_element
            --fzn-count 1 array_var_int_element --reference-std)
