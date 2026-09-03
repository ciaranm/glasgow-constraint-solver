predicate glasgow_circuit(array[int] of var int: x, int: offset);

% glasgow_circuit expects 0-based successors (a length-n array whose values are
% in 0..n-1), and FlatZinc circuit is defined over index_set(x) with successor
% values in that same set, so there is an offset of min(index_set(x)) rather than
% an assumed 1. It is passed rather than applied here: see fzn_subcircuit.mzn for
% why, which is that a comprehension would introduce a fresh full-domain variable
% per node and lose whatever the model had already narrowed. Circuit has no anchor
% to lose, since it always anchors on node 0, but the n variables and n linear
% constraints are worth not writing either way, and the two predicates are better
% off the same shape.
predicate fzn_circuit(array[int] of var int: x) =
    if length(x) = 0 then true
    else glasgow_circuit(x, min(index_set(x)))
    endif;
