include "globals.mzn";

% connected is reachable with the root existentially quantified, so this goes
% through the same override with a root MiniZinc introduces itself. The graph is
% a triangle with a tail, so there are node sets that are connected and node sets
% that are not.
array[1..4] of int: from = [1, 2, 1, 3];
array[1..4] of int: to = [2, 3, 3, 4];
array[1..4] of var bool: ns;
array[1..4] of var bool: es;

constraint connected(from, to, ns, es);

solve satisfy;

output ["ENUMSOL: " ++ show(ns) ++ " " ++ show(es)];
