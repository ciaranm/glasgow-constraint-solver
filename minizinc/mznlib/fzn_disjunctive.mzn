predicate glasgow_disjunctive(array[int] of var int: s,
    array[int] of var int: d);

predicate fzn_disjunctive(array[int] of var int: s,
    array[int] of var int: d) =
    forall(i in index_set(d)) (d[i] >= 0)
    /\ glasgow_disjunctive(s, d);
