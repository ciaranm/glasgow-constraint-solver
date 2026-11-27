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
