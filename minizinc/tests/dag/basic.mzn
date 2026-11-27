include "globals.mzn";

% Two triangles sharing a node, plus a spur no cycle can use, indexed from 2 on
% purpose: nodes are index_set(ns), which need not start at one, and the endpoint
% arrays are in that numbering.
array[1..7] of int: from = [2, 3, 4, 4, 5, 6, 6];
array[1..7] of int: to   = [3, 4, 2, 5, 6, 4, 7];
array[2..7] of var bool: ns;
array[1..7] of var bool: es;

% `subgraph` is posted alongside deliberately, and this test would fail without
% it. Dag enforces it and the stdlib's fzn_dag does not: its distance labelling
% only forces a selected edge's *head*, so the decomposition this is
% differential-tested against admits a selected edge leaving an unselected node
% and Dag does not. Posting it explicitly makes both readings the documented one
% --- "the subgraph ns and es ... is a DAG" --- so the solution sets agree and the
% test is about acyclicity rather than about that divergence. See
% dev_docs/minizinc.md.
constraint dag(from, to, ns, es);
constraint subgraph(from, to, ns, es);

solve satisfy;

output ["ENUMSOL: " ++ show(ns) ++ " " ++ show(es)];
