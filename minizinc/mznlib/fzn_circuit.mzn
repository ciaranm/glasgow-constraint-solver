predicate glasgow_circuit(array[int] of var int: x);
predicate fzn_circuit(array[int] of var int: x) = glasgow_circuit([x[i] - 1 | i in index_set(x)]);
