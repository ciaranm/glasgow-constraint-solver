# The reachability family. --fzn-pattern is the reachability guard: MiniZinc's
# connected / dconnected wrappers go through reachable / dreachable, so without
# it a test would still agree with the reference solver via the stdlib distance
# labelling even if the override never fired.
gcs_minizinc_test(minizinc-reachable basic.mzn true true OPTIONS --fzn-pattern glasgow_reachable)

gcs_minizinc_test(minizinc-connected connected_undirected.mzn true true OPTIONS --fzn-pattern glasgow_reachable)

gcs_minizinc_test(minizinc-dreachable dreachable.mzn true true OPTIONS --fzn-pattern glasgow_dreachable)

gcs_minizinc_test(minizinc-dconnected dconnected.mzn true true OPTIONS --fzn-pattern glasgow_dreachable)
