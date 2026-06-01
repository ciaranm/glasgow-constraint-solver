predicate glasgow_circuit(array[int] of var int: x);

% glasgow_circuit expects 0-based successors (a length-n array whose values are
% in 0..n-1). FlatZinc circuit is defined over index_set(x) with successor values
% in that same set, so shift by min(index_set(x)) rather than assuming 1-based.
predicate fzn_circuit(array[int] of var int: x) =
    glasgow_circuit([x[i] - min(index_set(x)) | i in index_set(x)]);
