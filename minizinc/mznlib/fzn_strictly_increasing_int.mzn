predicate glasgow_strictly_increasing_int(array[int] of var int: x);
predicate fzn_strictly_increasing_int(array[int] of var int: x) = glasgow_strictly_increasing_int(x);
