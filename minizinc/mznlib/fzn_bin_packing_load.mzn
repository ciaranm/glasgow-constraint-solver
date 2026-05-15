predicate glasgow_bin_packing_load(array[int] of var int: load,
    array[int] of var int: bin, array[int] of int: w);

predicate fzn_bin_packing_load(array[int] of var int: load,
    array[int] of var int: bin, array[int] of int: w) =
    let {
        int: lb = min(index_set(load));
    } in glasgow_bin_packing_load(
        [load[b] | b in index_set(load)],
        [bin[i] - lb | i in index_set(bin)],
        w);
