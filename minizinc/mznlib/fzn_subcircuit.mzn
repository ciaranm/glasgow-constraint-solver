predicate glasgow_subcircuit(array[int] of var int: x);

% glasgow_subcircuit expects 0-based successors (a length-n array whose values are
% in 0..n-1). FlatZinc subcircuit is defined over index_set(x) with successor
% values in that same set, so shift by min(index_set(x)) rather than assuming
% 1-based. The shift is consistent both ways: a node off the tour has x[i] = i,
% which after shifting is "the value equals the 0-based position".
%
% Keep the min inside the comprehension. The stdlib's fzn_subcircuit guards
% length(xs) = 0 explicitly and this override replaces that guard, but with an
% empty index set the comprehension body -- and so the min -- never evaluates, so
% the empty subcircuit still flattens. Hoisting the min into a let would turn it
% into a min-of-empty-set error.
predicate fzn_subcircuit(array[int] of var int: x) =
    glasgow_subcircuit([x[i] - min(index_set(x)) | i in index_set(x)]);
