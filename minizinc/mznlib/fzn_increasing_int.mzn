predicate glasgow_increasing_int(array[int] of var int: x);
predicate fzn_increasing_int(array[int] of var int: x) = glasgow_increasing_int(x);
