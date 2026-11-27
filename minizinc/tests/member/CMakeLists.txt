gcs_minizinc_test(minizinc-member basic.mzn true true)

# The shapes a front end hands member (#1006), over integers and over bools,
# which have builtins of their own, guarded by --fzn-count so that one rewritten
# away cannot hide behind the others: single elements, literals, a constant
# searched-for value, the searched-for value inside the array, negative-indexed
# 2-D arrays and enums. The empty array is unsatisfiable, so each type has a
# model of its own for it. reif.mzn has the reified, half-reified and negated
# contexts, which go through the stdlib's _reif decompositions and reach no
# builtin. --reference-std adds the standard library's decompositions, since
# MiniZinc's default solver has its own member.
gcs_minizinc_test(minizinc-member-shapes shapes.mzn true true
    OPTIONS --fzn-count 6 glasgow_member_int --reference-std)

gcs_minizinc_test(minizinc-member-bool-shapes bool_shapes.mzn true true
    OPTIONS --fzn-count 5 glasgow_member_bool --reference-std)

gcs_minizinc_test(minizinc-member-empty empty.mzn true true
    OPTIONS --unsatisfiable --fzn-count 1 glasgow_member_int --reference-std)

gcs_minizinc_test(minizinc-member-bool-empty bool_empty.mzn true true
    OPTIONS --unsatisfiable --fzn-count 1 glasgow_member_bool --reference-std)

gcs_minizinc_test(minizinc-member-reif reif.mzn true true OPTIONS --reference-std)
