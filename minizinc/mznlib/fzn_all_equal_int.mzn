predicate fzn_all_equal_int(array[int] of var int: x) =
    forall (i in index_set(x) where i + 1 in index_set(x)) (x[i] = x[i + 1]);
