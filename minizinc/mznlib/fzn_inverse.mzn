predicate glasgow_inverse(array[int] of var int: f, array[int] of var int: invf);
predicate fzn_inverse(array[int] of var int: f, array[int] of var int: invf) = glasgow_inverse(f, invf);
