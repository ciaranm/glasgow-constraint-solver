include "globals.mzn";

% An lbound above its ubound, which leaves no solution. The redefinition bounds
% a fresh count variable by both, and MiniZinc finds that empty while
% flattening, so the solver never runs.
array[1..3] of var 1..3: x;
constraint global_cardinality_low_up(x, [1, 2], [2, 1], [1, 2]);

solve satisfy;
output ["ENUMSOL: \(x)"];
