predicate glasgow_dpath(array[int] of int: from, array[int] of int: to, var int: s, var int: t,
    array[int] of var bool: ns, array[int] of var bool: es);

% As fzn_path_enum.mzn, but each edge may only be followed from its from to its
% to.
predicate fzn_dpath(array[int] of int: from, array[int] of int: to, var int: s, var int: t,
    array[int] of var bool: ns, array[int] of var bool: es) =
    let { int: offset = min(index_set(ns)) } in
    glasgow_dpath([from[e] - offset | e in index_set(from)],
                  [to[e] - offset | e in index_set(to)],
                  s - offset, t - offset,
                  [ns[n] | n in index_set(ns)],
                  [es[e] | e in index_set(es)]);
