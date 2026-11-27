include "globals.mzn";

% A triangle with a tail, indexed from 2 on purpose: nodes are index_set(ns),
% which need not start at one, and the endpoint arrays are in that numbering.
array[1..4] of int: from = [2, 3, 2, 4];
array[1..4] of int: to = [3, 4, 4, 5];
array[2..5] of var bool: ns;
array[1..4] of var bool: es;

constraint subgraph(from, to, ns, es);

solve satisfy;

output ["ENUMSOL: " ++ show(ns) ++ " " ++ show(es)];
