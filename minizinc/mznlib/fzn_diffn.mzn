predicate glasgow_diffn(array[int] of var int: x, array[int] of var int: y,
    array[int] of var int: dx, array[int] of var int: dy);

predicate glasgow_diffn_nonstrict(array[int] of var int: x, array[int] of var int: y,
    array[int] of var int: dx, array[int] of var int: dy);

predicate fzn_diffn(array[int] of var int: x, array[int] of var int: y,
    array[int] of var int: dx, array[int] of var int: dy) =
    glasgow_diffn(x, y, dx, dy);
