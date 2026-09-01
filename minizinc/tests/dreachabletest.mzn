include "globals.mzn";

% The same four-node path, but directed, so only the nodes at or after the root
% can be selected.
array[1..3] of int: from = [1, 2, 3];
array[1..3] of int: to = [2, 3, 4];
array[1..4] of var bool: ns;
array[1..3] of var bool: es;
var 1..4: r;

constraint dreachable(from, to, r, ns, es);

solve satisfy;

output ["ENUMSOL: " ++ show(r) ++ " " ++ show(ns) ++ " " ++ show(es)];
