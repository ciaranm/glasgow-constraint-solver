include "globals.mzn";

% An empty selection from an empty graph is a subgraph, so this has the two
% solutions of y (#1303). The four-argument subgraph reaches
% fzn_subgraph_enum.mzn whatever the index sets, and that redefinition used to
% take min(index_set(ns)) of an empty set, which MiniZinc reads as false in a
% Boolean context, and report UNSATISFIABLE.
array[1..0] of int: from = [];
array[1..0] of int: to = [];
array[1..0] of var bool: ns;
array[1..0] of var bool: es;
var 1..3: y;
constraint y != 2;
constraint subgraph(from, to, ns, es);

solve satisfy;

output ["ENUMSOL: \(y)"];
