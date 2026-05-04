predicate glasgow_all_different_except_int(array[int] of var int: vs, set of int: S);
predicate fzn_alldifferent_except(array[int] of var int: vs, set of int: S) = glasgow_all_different_except_int(vs, S);
