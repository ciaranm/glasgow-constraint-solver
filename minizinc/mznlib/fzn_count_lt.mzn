predicate fzn_count_lt(array[int] of var int: x, var int: y, var int: c) =
    let { var 0..length(x): z } in glasgow_count_eq(x, y, z) /\ z > c;
