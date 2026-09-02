predicate glasgow_dtree(array[int] of int: from, array[int] of int: to, var int: r,
    array[int] of var bool: ns, array[int] of var bool: es);

% As fzn_tree_enum.mzn, but each edge may only be followed from its from to its
% to, so the selected subgraph is an arborescence rooted at r.
predicate fzn_dtree(array[int] of int: from, array[int] of int: to, var int: r,
    array[int] of var bool: ns, array[int] of var bool: es) =
    let { int: offset = min(index_set(ns)) } in
    glasgow_dtree([from[e] - offset | e in index_set(from)],
                  [to[e] - offset | e in index_set(to)],
                  r - offset,
                  [ns[n] | n in index_set(ns)],
                  [es[e] | e in index_set(es)]);
