predicate glasgow_among(var int: n, array[int] of var int: x, set of int: v);
predicate fzn_among(var int: n, array[int] of var int: x, set of int: v) = glasgow_among(n, x, v);
