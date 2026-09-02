predicate glasgow_subcircuit(array[int] of var int: x, int: offset);

% glasgow_subcircuit expects 0-based successors (a length-n array whose values
% are in 0..n-1), and FlatZinc subcircuit is defined over index_set(x) with
% successor values in that same set. So there is an offset, min(index_set(x))
% rather than an assumed 1, and it is passed rather than applied here.
%
% Applying it here -- `[x[i] - min(index_set(x)) | i in index_set(x)]` -- is what
% this used to do, and it is a worse idea than it looks. The comprehension
% introduces a fresh FlatZinc variable per node, declared over the full range
% before its defining constraint has propagated, so every narrowing the model had
% already made to x is invisible to the constraint. SubCircuit cares about
% precisely one such narrowing: a node whose own index has been taken out of its
% domain is a node known to be on the tour, which is what lets it anchor the
% position encoding. `constraint succ[n] != n` -- which is how the tpp challenge
% model says it -- narrows x and then loses it in the shift.
%
% gcs applies the offset as a view instead, so the domains survive, and n
% variables and n linear constraints do not get written into the FlatZinc at all.
%
% The shift is consistent both ways: a node off the tour has x[i] = i, which after
% shifting is "the value equals the 0-based position".
%
% Keep the min inside the call. The stdlib's fzn_subcircuit guards length(xs) = 0
% explicitly and this override replaces that guard; with an empty index set the
% min would be a min-of-empty-set error, so it is guarded here instead.
predicate fzn_subcircuit(array[int] of var int: x) =
    if length(x) = 0 then true
    else glasgow_subcircuit(x, min(index_set(x)))
    endif;
