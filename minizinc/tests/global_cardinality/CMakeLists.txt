gcs_minizinc_test(minizinc-globalcardinality basic.mzn true true)

gcs_minizinc_test(minizinc-globalcardinalityclosed closed.mzn true true)

gcs_minizinc_test(minizinc-globalcardinalitylowup low_up.mzn true true)

# The magic sequence, where every count is one of the counted variables (#1191).
# The solutions were right; it is the proof run that tests anything here.
gcs_minizinc_test(minizinc-globalcardinalitymagic magic.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_global_cardinality)

# A cover that repeats a value, which MiniZinc permits and GlobalCardinality does
# not: the front end folds the repeat out and posts the count equality it stood
# for (#922). The fzn pattern is what stops these passing vacuously -- if the
# repeat were folded by MiniZinc's own wrapper instead, the solutions would still
# agree and the builtin under test would never have run.
gcs_minizinc_test(minizinc-globalcardinalityrepeated repeated.mzn true true
    OPTIONS --fzn-pattern glasgow_global_cardinality)

gcs_minizinc_test(minizinc-globalcardinalityrepeatedclosed repeated_closed.mzn true true
    OPTIONS --fzn-pattern glasgow_global_cardinality_closed)

# A par entry in the variable array, which the front end posts as a constant in
# GlobalCardinality's scope (#1046). With proofs the open model aborted and the
# closed model's proof was rejected; the solutions were right either way, so it
# is the proof run that tests anything here.
gcs_minizinc_test(minizinc-globalcardinalityconstant constant.mzn true true
    OPTIONS --fzn-pattern glasgow_global_cardinality)

gcs_minizinc_test(minizinc-globalcardinalityconstantclosed constant_closed.mzn true true
    OPTIONS --fzn-pattern glasgow_global_cardinality_closed)

# The shapes a front end can misread (#1006), several to a model: negative cover
# values and ones outside every domain, cover and counts indexed from 0 or -1, a
# two-dimensional x, an empty cover, integer literals and repeated variables in
# x, enums, zero bounds and an ubound past length(x) in the low/up forms. Each
# count insists that every shape reached its builtin; the `[^_]` keeps the open
# form's pattern from also matching the closed one. An empty x never reaches a
# builtin, since the stdlib's wrapper decides it. --reference-std adds the
# standard library's decompositions, since MiniZinc's default solver has its own
# global_cardinality. The low/up lanes are what notice a redefinition that drops
# a bound or starts the counts at 1.
gcs_minizinc_test(minizinc-globalcardinality-shapes shapes.mzn true true
    OPTIONS --fzn-count 5 "glasgow_global_cardinality[^_]" --reference-std)

gcs_minizinc_test(minizinc-globalcardinality-closedshapes closed_shapes.mzn true true
    OPTIONS --fzn-count 3 glasgow_global_cardinality_closed --reference-std)

gcs_minizinc_test(minizinc-globalcardinality-lowupshapes low_up_shapes.mzn true true
    OPTIONS --fzn-count 2 "glasgow_global_cardinality[^_]" --fzn-count 2 glasgow_global_cardinality_closed
        --reference-std)

# A negative lbound, which MiniZinc's default solver gets wrong in both low/up
# forms: global_cardinality_low_up(x, [1], [-1], [2]) over two variables in
# 1..2 has four solutions and it reports UNSATISFIABLE. So this compares against
# the standard library's decompositions alone.
gcs_minizinc_test(minizinc-globalcardinality-lowupnegative low_up_negative.mzn true true
    OPTIONS --fzn-count 1 "glasgow_global_cardinality[^_]" --fzn-count 1 glasgow_global_cardinality_closed
        --reference-std --skip-default-reference)

# Closed forms with no solution, which the solver has to prove: an integer
# literal outside the cover, and an empty cover over a non-empty x.
gcs_minizinc_test(minizinc-globalcardinality-closedforcedout closed_forced_out.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_global_cardinality_closed --reference-std)

gcs_minizinc_test(minizinc-globalcardinality-closedemptycover closed_empty_cover.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_global_cardinality_closed --reference-std)

# An lbound above its ubound. MiniZinc finds the inconsistency while flattening,
# so no solver runs and there is no proof to check.
gcs_minizinc_test(minizinc-globalcardinality-lowupcrossed low_up_crossed.mzn true false
    OPTIONS --unsatisfiable --reference-std)

# Reified, half-reified and negated calls of all four forms, which reach the
# stdlib's reified decompositions rather than a builtin, so there is nothing to
# count; the lane checks that they flatten and agree.
gcs_minizinc_test(minizinc-globalcardinality-reif reif.mzn true true)
