include "globals.mzn";

% A fixed root that is not a node. The N-and-E spelling's nodes are 1..N, so
% fzn_reachable_int.mzn hands the builtin a root of -1, which Reachable has to
% answer as unsatisfiable, with a proof, rather than reject or read as an
% index.
array[1..2] of int: f = [1, 2];
array[1..2] of int: t = [2, 3];
array[1..3] of var bool: ns;
array[1..2] of var bool: es;

constraint reachable(3, 2, f, t, 0, ns, es);

solve satisfy;

output ["ENUMSOL: \(ns) \(es)"];
