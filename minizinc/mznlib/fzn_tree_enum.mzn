predicate glasgow_tree(array[int] of int: from, array[int] of int: to, var int: r,
    array[int] of var bool: ns, array[int] of var bool: es);

% glasgow_tree numbers nodes from zero, takes edge e's endpoints as from[e] and
% to[e], and follows each edge either way. Nodes are shifted to zero exactly as
% fzn_reachable_enum.mzn shifts them, and for the same reason.
%
% Going straight to glasgow_tree rather than doubling the edges into fzn_dtree
% is deliberate, and matters more here than it does for reachability: Tree posts
% one reachability encoding, whose size is O(nodes * edges), so doubling the edge
% set would double it for nothing. The propagator follows an undirected edge both
% ways itself.
predicate fzn_tree(array[int] of int: from, array[int] of int: to, var int: r,
    array[int] of var bool: ns, array[int] of var bool: es) =
    let { int: offset = min(index_set(ns)) } in
    glasgow_tree([from[e] - offset | e in index_set(from)],
                 [to[e] - offset | e in index_set(to)],
                 r - offset,
                 [ns[n] | n in index_set(ns)],
                 [es[e] | e in index_set(es)]);
