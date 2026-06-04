predicate glasgow_diffn(array[int] of var int: x, array[int] of var int: y,
    array[int] of int: dx, array[int] of int: dy);

predicate glasgow_diffn_nonstrict(array[int] of var int: x, array[int] of var int: y,
    array[int] of int: dx, array[int] of int: dy);

predicate fzn_diffn(array[int] of var int: x, array[int] of var int: y,
    array[int] of var int: dx, array[int] of var int: dy) =
    glasgow_diffn(x, y,
        [fix(dx[i]) | i in index_set(dx)],
        [fix(dy[i]) | i in index_set(dy)]);
