predicate glasgow_subgraph(array[int] of int: from, array[int] of int: to,
    array[int] of var bool: ns, array[int] of var bool: es);

% glasgow_subgraph numbers nodes from zero and takes edge e's endpoints as
% from[e] and to[e]. FlatZinc's nodes are index_set(ns), which need not start at
% one, so shift the endpoints by the same offset, as fzn_reachable_enum.mzn does.
% The endpoint arrays are parameters, so the shift is free.
%
% With no nodes, min(index_set(ns)) is undefined, which MiniZinc would read as
% false and so report an empty selection as unsatisfiable (#1303). This file is
% what the four-argument subgraph reaches whatever its index sets, not just
% enums. subgraph.mzn's asserts leave no edges in that case; one passed to
% fzn_subgraph directly has an endpoint that is not a node, so it is left out,
% as the standard library's own decomposition reads it. The rooted graph
% overrides want the opposite guard (see dev_docs/minizinc.md).
predicate fzn_subgraph(array[int] of int: from, array[int] of int: to,
    array[int] of var bool: ns, array[int] of var bool: es) =
    if length(ns) = 0 then forall (e in index_set(es)) (not es[e])
    else
        let { int: offset = min(index_set(ns)) } in
        glasgow_subgraph([from[e] - offset | e in index_set(from)],
                         [to[e] - offset | e in index_set(to)],
                         [ns[n] | n in index_set(ns)],
                         [es[e] | e in index_set(es)])
    endif;
