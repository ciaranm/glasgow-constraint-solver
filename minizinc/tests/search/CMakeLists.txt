gcs_minizinc_test(minizinc-seqwdeg wdeg.mzn true true)

gcs_minizinc_test(minizinc-splitrandom split_random.mzn true true)

# Search annotations (#1006). fzn_glasgow.cc reads int_search, bool_search and
# seq_search, maps the heuristics it knows, warns and falls back on the rest,
# and ignores everything under -f. A complete search must enumerate the same
# solutions whatever it does, so these lanes are about a value order that loses
# or repeats a value, an annotation shape the reader trips over, and -f itself;
# the counts pin that the flattener handed every annotation over.
gcs_minizinc_test(minizinc-search-heuristics heuristics.mzn true true
    OPTIONS --fzn-count 12 "\"int_search\"" --reference-std)

gcs_minizinc_test(minizinc-search-heuristics-free heuristics.mzn true true
    OPTIONS --fzn-count 12 "\"int_search\""
    FLAGS "-f")

gcs_minizinc_test(minizinc-search-nested nested.mzn true true
    OPTIONS --fzn-count 6 "\"int_search\"" --fzn-count 2 "\"bool_search\"" --fzn-count 3 "\"seq_search\"" --reference-std)

gcs_minizinc_test(minizinc-search-nested-free nested.mzn true true
    OPTIONS --fzn-count 6 "\"int_search\"" --fzn-count 2 "\"bool_search\"" --fzn-count 3 "\"seq_search\""
    FLAGS "-f")
