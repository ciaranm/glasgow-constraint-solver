predicate glasgow_increasing_bool(array[int] of var bool: x);
predicate fzn_increasing_bool(array[int] of var bool: x) = glasgow_increasing_bool(x);
