predicate glasgow_count_eq(array[int] of var int: x, var int: y, var int: c);
predicate fzn_count_eq(array[int] of var int: x, var int: y, var int: c) = glasgow_count_eq(x, y, c);
