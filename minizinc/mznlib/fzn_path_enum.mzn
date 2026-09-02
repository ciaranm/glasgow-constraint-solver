predicate glasgow_path(array[int] of int: from, array[int] of int: to, var int: s, var int: t,
    array[int] of var bool: ns, array[int] of var bool: es);

% As fzn_tree_enum.mzn, with both endpoints shifted rather than one root. The
% stdlib's fzn_path doubles the edges and then asks for two spanning trees; one
% reachability encoding plus degree bounds says the same thing.
predicate fzn_path(array[int] of int: from, array[int] of int: to, var int: s, var int: t,
    array[int] of var bool: ns, array[int] of var bool: es) =
    let { int: offset = min(index_set(ns)) } in
    glasgow_path([from[e] - offset | e in index_set(from)],
                 [to[e] - offset | e in index_set(to)],
                 s - offset, t - offset,
                 [ns[n] | n in index_set(ns)],
                 [es[e] | e in index_set(es)]);
