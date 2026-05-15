predicate glasgow_bin_packing_capa(array[int] of int: c,
    array[int] of var int: bin, array[int] of int: w);

predicate fzn_bin_packing(int: c, array[int] of var int: bin,
    array[int] of int: w) =
    if length(bin) > 0 then
        let {
            int: lb = lb_array(bin);
            int: ub = ub_array(bin);
        } in glasgow_bin_packing_capa(
            [c | b in lb..ub],
            [bin[i] - lb | i in index_set(bin)],
            w)
    endif;
