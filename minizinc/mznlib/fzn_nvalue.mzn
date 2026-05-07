predicate glasgow_nvalue(var int: n, array[int] of var int: x);
predicate fzn_nvalue(var int: n, array[int] of var int: x) = glasgow_nvalue(n, x);
