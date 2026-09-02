include "globals.mzn";

% A triangle with a tail, indexed from 2, so that both "this is a tree" and
% "this has a cycle in it" are reachable node sets. The root is a variable, as
% tree's signature has it.
array[1..4] of int: from = [2, 3, 2, 4];
array[1..4] of int: to = [3, 4, 4, 5];
array[2..5] of var bool: ns;
array[1..4] of var bool: es;
var 2..5: r;

constraint tree(from, to, r, ns, es);

solve satisfy;

output ["ENUMSOL: " ++ show(r) ++ " " ++ show(ns) ++ " " ++ show(es)];
