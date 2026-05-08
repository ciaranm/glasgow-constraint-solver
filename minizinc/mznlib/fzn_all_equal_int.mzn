predicate glasgow_all_equal_int(array[int] of var int: x);
predicate fzn_all_equal_int(array[int] of var int: x) = glasgow_all_equal_int(x);
