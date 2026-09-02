predicate glasgow_subgraph(array[int] of int: from, array[int] of int: to,
    array[int] of var bool: ns, array[int] of var bool: es);

% glasgow_subgraph numbers nodes from zero and takes edge e's endpoints as
% from[e] and to[e]. FlatZinc's nodes are index_set(ns), which need not start at
% one, so shift the endpoints by the same offset, as fzn_reachable_enum.mzn does.
% The endpoint arrays are parameters, so the shift is free.
predicate fzn_subgraph(array[int] of int: from, array[int] of int: to,
    array[int] of var bool: ns, array[int] of var bool: es) =
    let { int: offset = min(index_set(ns)) } in
    glasgow_subgraph([from[e] - offset | e in index_set(from)],
                     [to[e] - offset | e in index_set(to)],
                     [ns[n] | n in index_set(ns)],
                     [es[e] | e in index_set(es)]);
