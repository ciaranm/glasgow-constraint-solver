predicate glasgow_cumulative(array[int] of var int: s,
    array[int] of int: d, array[int] of int: r, int: b);

predicate fzn_cumulative(array[int] of var int: s,
    array[int] of var int: d, array[int] of var int: r,
    var int: b) =
    glasgow_cumulative(s,
        [fix(d[i]) | i in index_set(d)],
        [fix(r[i]) | i in index_set(r)],
        fix(b));
