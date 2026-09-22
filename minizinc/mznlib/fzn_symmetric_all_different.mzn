predicate glasgow_symmetric_all_different(array[int] of var int: x, int: start);

% symmetric_all_different is an involution on x's own index set: x[i] = j if and
% only if x[j] = i, with every value in index_set(x). SymmetricAllDifferent takes
% the first element of that set as its start, so it is min(index_set(x)) rather
% than an assumed 1, and it has to be passed from here: FlatZinc arrays are
% 1-based, so the flattened call no longer carries the model's index set. Passing
% 1 regardless enforced the 1-based involution on a 0-based array, which reads its
% values shifted by one --- wrong solutions, or a wrong UNSATISFIABLE that the
% proof then certified, since the proof starts after this point.
%
% With an empty index set the min would be undefined, so that case is guarded, as
% fzn_circuit.mzn does. The empty array is trivially an involution.
predicate fzn_symmetric_all_different(array[int] of var int: x) =
    if length(x) = 0 then true
    else glasgow_symmetric_all_different(x, min(index_set(x)))
    endif;
