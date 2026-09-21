predicate glasgow_inverse(array[int] of var int: f, array[int] of var int: invf,
    int: f_start, int: invf_start);

% f's values are indices of invf and invf's values are indices of f, over
% whatever index sets the model gave them, so each array's first index is passed
% as one of Inverse's two starts. See fzn_symmetric_all_different.mzn for why it
% has to be passed from here rather than assumed to be 1.
%
% Arrays of different lengths cannot be inverse to one another, since each is
% then an injection into the other's index set; that is what the stdlib
% decomposition says, and saying it here also covers exactly one array being
% empty, where a min would be undefined. Two empty arrays are trivially inverse.
predicate fzn_inverse(array[int] of var int: f, array[int] of var int: invf) =
    if length(f) != length(invf) then false
    elseif length(f) = 0 then true
    else glasgow_inverse(f, invf, min(index_set(f)), min(index_set(invf)))
    endif;
