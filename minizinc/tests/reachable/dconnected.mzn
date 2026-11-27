include "globals.mzn";

% dconnected asks for some selected node that reaches every selected node, which
% on this directed triangle-with-a-tail is a genuinely different requirement from
% connected: the tail can only be reached from node 3.
array[1..4] of int: from = [1, 2, 1, 3];
array[1..4] of int: to = [2, 3, 3, 4];
array[1..4] of var bool: ns;
array[1..4] of var bool: es;

constraint dconnected(from, to, ns, es);

solve satisfy;

output ["ENUMSOL: " ++ show(ns) ++ " " ++ show(es)];
