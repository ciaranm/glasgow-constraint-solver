predicate glasgow_bin_packing_capa(array[int] of int: c,
    array[int] of var int: bin, array[int] of int: w);

predicate fzn_bin_packing_capa(array[int] of int: c,
    array[int] of var int: bin, array[int] of int: w) =
    let {
        int: lb = min(index_set(c));
    } in glasgow_bin_packing_capa(
        [c[b] | b in index_set(c)],
        [bin[i] - lb | i in index_set(bin)],
        w);
