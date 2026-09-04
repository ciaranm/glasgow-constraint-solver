predicate glasgow_bin_packing_capa(array[int] of int: c,
    array[int] of var int: bin, array[int] of int: w, int: offset);

% gcs's BinPacking numbers bins 0..num_bins-1 and rejects an item whose domain
% leaves that range, so there is an offset. It is passed rather than applied
% here: see fzn_bin_packing_capa.mzn for why a comprehension over bin is the
% wrong way to apply it.
%
% Here the bins are the values bin can take, so the offset is lb_array(bin) and
% the capacity array is built over that same range.
predicate fzn_bin_packing(int: c, array[int] of var int: bin,
    array[int] of int: w) =
    if length(bin) = 0 then true
    else
        let {
            int: lb = lb_array(bin);
            int: ub = ub_array(bin);
        } in glasgow_bin_packing_capa([c | b in lb..ub], bin, w, lb)
    endif;
