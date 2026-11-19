# element_stress (experiment only, not for merging)

Random `y = A[i][j]` (2D) or `y = A[i][j][k]` (3D) Element instances. These were
used to compare a nested chain of `cases` steps (one per index, the default here)
with one flat `cases` step over every index's equality literals, when checking
VeriPB MR !240 (cases rule with tree search).

The Element justification is chosen at run time:

    GCS_ELEMENT_CASES=nested   # default: the existing per-index chain
    GCS_ELEMENT_CASES=flat     # one cases line over all index literals

The runs quoted in VeriPB commit "cases: avoid checks at tree nodes that cannot
close early" used constant arrays, entries uniform in 0..1000, seed 1, and stopped
after 3 solutions:

    GCS_ELEMENT_CASES=flat element_stress --prove --dims 2 -n 160 --seed 1 --constant \
        -k 1000 --max-solutions 3 --proof-files-basename flat_d2_n160_s1
    veripb --force-checked-deletion flat_d2_n160_s1.opb flat_d2_n160_s1.pbp

and the same with `--dims 3 -n 10|20|30`, and with `GCS_ELEMENT_CASES=nested`.

Without `--constant`, array entries are variables with random domains in
`lo..lo+k/2`. `3D` uses `NDimensionalElement<_, 3>` directly with GAC.
