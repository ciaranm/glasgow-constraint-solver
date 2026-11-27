include "globals.mzn";

% A negative lbound, which says nothing: a value may occur at least -1 times.
% MiniZinc's default solver gets this wrong in both forms (one solution where
% there are three of each), so the lane compares against the standard library's
% decompositions alone.
array[1..3] of var 1..3: x;
constraint global_cardinality_low_up(x, [1, 2, 3], [-1, 0, 1], [5, 0, 1]);

array[1..2] of var 1..3: y;
constraint global_cardinality_low_up_closed(y, [1, 3], [-2, 1], [1, 2]);

solve satisfy;
output ["ENUMSOL: \(x) \(y)"];
