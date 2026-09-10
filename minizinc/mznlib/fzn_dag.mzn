predicate glasgow_dag(array[int] of int: from, array[int] of int: to,
    array[int] of var bool: ns, array[int] of var bool: es);

% glasgow_dag numbers nodes from zero and takes edge e's tail and head as from[e]
% and to[e]. FlatZinc's nodes are index_set(ns), which need not start at one, so
% shift the endpoints by the same offset, as fzn_subgraph.mzn does. The endpoint
% arrays are parameters, so the shift is free.
%
% Unlike the rest of globals.graph there is no _int / _enum pair to override:
% dag.mzn does the enum2int itself and calls a single fzn_dag. There is no
% reified form either -- the stdlib's fzn_dag_reif is an abort.
%
% Note that this is stricter than the stdlib decomposition it replaces. The
% documented meaning is "the subgraph ns and es ... is a DAG", but the stdlib's
% distance labelling only forces an edge's head to be selected, so it admits a
% selected edge leaving an unselected node. Dag follows the documentation and
% fzn_dreachable, which calls subgraph explicitly. See dev_docs/minizinc.md.
predicate fzn_dag(array[int] of int: from, array[int] of int: to,
    array[int] of var bool: ns, array[int] of var bool: es) =
    let { int: offset = min(index_set(ns)) } in
    glasgow_dag([from[e] - offset | e in index_set(from)],
                [to[e] - offset | e in index_set(to)],
                [ns[n] | n in index_set(ns)],
                [es[e] | e in index_set(es)]);
