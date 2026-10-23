predicate glasgow_dag(array[int] of int: from, array[int] of int: to,
    array[int] of var bool: ns, array[int] of var bool: es);

% glasgow_dag numbers nodes from zero and takes edge e's tail and head as from[e]
% and to[e]. FlatZinc's nodes are index_set(ns), which need not start at one, so
% shift the endpoints by the same offset, as fzn_subgraph_enum.mzn does. The endpoint
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
%
% With no nodes, min(index_set(ns)) is undefined, which MiniZinc would read as
% false and so report an empty graph as unsatisfiable (#1303). The empty graph
% is a DAG, so the guard holds. dag.mzn's asserts leave no edges in that case;
% one passed to fzn_dag directly has an endpoint that is not a node, so it is
% left out, as the standard library's own fzn_dag reads it.
predicate fzn_dag(array[int] of int: from, array[int] of int: to,
    array[int] of var bool: ns, array[int] of var bool: es) =
    if length(ns) = 0 then forall (e in index_set(es)) (not es[e])
    else
        let { int: offset = min(index_set(ns)) } in
        glasgow_dag([from[e] - offset | e in index_set(from)],
                    [to[e] - offset | e in index_set(to)],
                    [ns[n] | n in index_set(ns)],
                    [es[e] | e in index_set(es)])
    endif;
