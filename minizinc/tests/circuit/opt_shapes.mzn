include "globals.mzn";

% circuit over optional successors has no override of its own: the standard
% library's fzn_circuit_opt turns it into a subcircuit in which an absent
% successor is a node off the tour, and that subcircuit reaches our
% redefinition. So this is subcircuit's offset again, from -1 and from 5,
% through a wrapper that builds the array itself, plus a successor that is
% absent as a literal. MiniZinc warns that deopt of that literal is undefined;
% the wrapper guards it with occurs, and every solver gets the same warning.
array[-1..2] of var opt -1..2: x;
var opt 5..7: a;
var opt 5..7: b;

constraint circuit(x);
constraint circuit(array1d(5..7, [a, <>, b]));

solve satisfy;

output ["ENUMSOL: \(x) \(a) \(b)"];
