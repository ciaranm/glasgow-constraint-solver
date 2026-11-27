include "globals.mzn";

% The same graph read as arcs, so that the in-degree rule has something to do:
% node 4 can be entered from 3 or from 2, and an arborescence uses one of them.
array[1..4] of int: from = [2, 3, 2, 4];
array[1..4] of int: to = [3, 4, 4, 5];
array[2..5] of var bool: ns;
array[1..4] of var bool: es;
var 2..5: r;

constraint dtree(from, to, r, ns, es);

solve satisfy;

output ["ENUMSOL: " ++ show(r) ++ " " ++ show(ns) ++ " " ++ show(es)];
