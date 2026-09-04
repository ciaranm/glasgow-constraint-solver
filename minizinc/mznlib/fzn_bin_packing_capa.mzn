predicate glasgow_bin_packing_capa(array[int] of int: c,
    array[int] of var int: bin, array[int] of int: w, int: offset);

% gcs's BinPacking numbers bins 0..num_bins-1, so the bin variables have to be
% shifted by min(index_set(c)). The offset is passed and gcs applies it as a
% view, rather than being applied here.
%
% Applying it here -- `[bin[i] - lb | i in index_set(bin)]` -- is what this used
% to do, and it is a worse idea than it looks. The comprehension introduces a
% fresh FlatZinc variable per item, declared over the full range before its
% defining int_lin_eq has propagated, and gcs's LinearEquality is bounds
% consistent by default. So a hole punched in either copy crossed to the other
% only as a bound: BinPacking prunes by removing individual bins from an item's
% domain, and a search annotation names the model's own array, so both the
% pruning and the brancher's view of the domain sizes were lost in the shift.
%
% A view keeps the domain, because a view is the same variable, and n variables
% and n linear constraints never get written into the FlatZinc at all.
%
% Keep the min inside the call, guarded: with an empty capacity array the min
% would be a min-of-empty-set error, and no bins is satisfiable exactly when
% there are no items to place.
predicate fzn_bin_packing_capa(array[int] of int: c,
    array[int] of var int: bin, array[int] of int: w) =
    if length(c) = 0 then length(bin) = 0
    else glasgow_bin_packing_capa(c, bin, w, min(index_set(c)))
    endif;
