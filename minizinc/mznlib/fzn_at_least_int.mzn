predicate fzn_at_least_int(int: n, array[int] of var int: x, int: v) =
    let { var 0..length(x): z } in glasgow_count_eq(x, v, z) /\ z >= n;
