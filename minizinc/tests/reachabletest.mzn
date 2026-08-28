include "globals.mzn";

% A four-node path, indexed from 2 on purpose: nodes are index_set(ns), which
% need not start at one, and the endpoint arrays and the root are in that same
% numbering. A shift that assumed 1-based nodes would turn satisfiable
% instances into spurious UNSAT, as it once did for circuit.
array[1..3] of int: from = [2, 3, 4];
array[1..3] of int: to = [3, 4, 5];
array[2..5] of var bool: ns;
array[1..3] of var bool: es;
var 2..5: r;

constraint reachable(from, to, r, ns, es);

solve satisfy;

output ["ENUMSOL: " ++ show(r) ++ " " ++ show(ns) ++ " " ++ show(es)];
