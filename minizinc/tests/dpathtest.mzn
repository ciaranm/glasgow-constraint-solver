include "globals.mzn";

% The same graph read as arcs, so the in and out degree rules both matter.
array[1..5] of int: from = [2, 3, 2, 4, 3];
array[1..5] of int: to = [3, 4, 4, 5, 5];
array[2..5] of var bool: ns;
array[1..5] of var bool: es;
var 2..5: s;
var 2..5: t;

constraint dpath(from, to, s, t, ns, es);

solve satisfy;

output ["ENUMSOL: " ++ show(s) ++ " " ++ show(t) ++ " " ++ show(ns) ++ " " ++ show(es)];
