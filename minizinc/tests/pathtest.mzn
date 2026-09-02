include "globals.mzn";

% Two ways round from 2 to 5, plus a chord, so the degree rules matter. Both
% endpoints are variables, including the start = end case that collapses the
% path to a single node.
array[1..5] of int: from = [2, 3, 2, 4, 3];
array[1..5] of int: to = [3, 4, 4, 5, 5];
array[2..5] of var bool: ns;
array[1..5] of var bool: es;
var 2..5: s;
var 2..5: t;

constraint path(from, to, s, t, ns, es);

solve satisfy;

output ["ENUMSOL: " ++ show(s) ++ " " ++ show(t) ++ " " ++ show(ns) ++ " " ++ show(es)];
