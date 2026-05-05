predicate glasgow_symmetric_all_different(array[int] of var int: x);
predicate fzn_symmetric_all_different(array[int] of var int: x) = glasgow_symmetric_all_different(x);
