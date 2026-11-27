include "globals.mzn";

% reachable over no nodes is unsatisfiable, because the root has to be a
% selected node. This is the enum spelling, whose redefinition takes
% min(index_set(ns)) unguarded; MiniZinc reads that as false, which is the right
% answer here, so the flattener reports it and no solver runs. A guard of
% `then true` copied from circuit or subgraph would turn it into a wrong
% solution (#1305). The N-and-E spelling of the same thing is a solver error
% (#1305), and has no lane until that is fixed.
array[1..0] of int: f = [];
array[1..0] of int: t = [];
array[1..0] of var bool: ns;
array[1..0] of var bool: es;
var 1..3: r;

constraint reachable(f, t, r, ns, es);

solve satisfy;

output ["ENUMSOL: \(r)"];
