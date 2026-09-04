predicate glasgow_bin_packing_load(array[int] of var int: load,
    array[int] of var int: bin, array[int] of int: w, int: offset);

% As fzn_bin_packing_capa.mzn, which carries the reasoning: the offset is
% passed and applied as a view rather than shifting bin in a comprehension,
% which would lose every hole the propagator punches.
%
% The load array needs no such care. `[load[b] | b in index_set(load)]` was
% already free -- with no arithmetic in the comprehension the flattener reuses
% the same variables rather than introducing new ones -- but it is dropped here
% too, since passing load directly says so rather than relying on it.
predicate fzn_bin_packing_load(array[int] of var int: load,
    array[int] of var int: bin, array[int] of int: w) =
    if length(load) = 0 then length(bin) = 0
    else glasgow_bin_packing_load(load, bin, w, min(index_set(load)))
    endif;
