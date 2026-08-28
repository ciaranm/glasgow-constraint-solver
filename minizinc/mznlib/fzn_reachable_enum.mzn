predicate glasgow_reachable(array[int] of int: from, array[int] of int: to, var int: r,
    array[int] of var bool: ns, array[int] of var bool: es);

% glasgow_reachable numbers nodes from zero, takes edge e's endpoints as from[e]
% and to[e], and follows each edge either way. FlatZinc's nodes are index_set(ns),
% which need not start at one --- an enum-indexed model starts wherever the enum
% does --- so shift the endpoints and the root by the same offset, as
% fzn_circuit.mzn does with successors. The endpoint arrays are parameters, so
% their shift is free; only the root costs an auxiliary.
%
% Going straight to glasgow_reachable rather than doubling the edges into
% fzn_dreachable is deliberate: the propagator follows an undirected edge both
% ways itself, so doubling would give it two edge variables aliasing one
% FlatZinc variable for no gain.
predicate fzn_reachable(array[int] of int: from, array[int] of int: to, var int: r,
    array[int] of var bool: ns, array[int] of var bool: es) =
    let { int: offset = min(index_set(ns)) } in
    glasgow_reachable([from[e] - offset | e in index_set(from)],
                      [to[e] - offset | e in index_set(to)],
                      r - offset,
                      [ns[n] | n in index_set(ns)],
                      [es[e] | e in index_set(es)]);
