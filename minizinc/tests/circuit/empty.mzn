include "globals.mzn";

% An empty circuit is vacuously true, so this has the two solutions of y. The
% redefinition guards length(x) = 0, because min of an empty index set is
% undefined, which MiniZinc reads as false and would report as UNSATISFIABLE.
% Gecode's own fzn_circuit has exactly that missing guard, so the default
% solver gets this wrong.
array[1..0] of var 1..3: none;
var 1..3: y;

constraint y != 2;
constraint circuit(none);

solve satisfy;

output ["ENUMSOL: \(y)"];
