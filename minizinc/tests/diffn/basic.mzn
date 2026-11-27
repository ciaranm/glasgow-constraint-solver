include "globals.mzn";

% Pack three rectangles of fixed size into a small grid with no overlap,
% exercising glasgow_diffn end to end. Enumerated against the default solver.
int: n = 3;
array[1..n] of int: w = [2, 1, 1];
array[1..n] of int: h = [1, 2, 1];

array[1..n] of var 0..2: x;
array[1..n] of var 0..2: y;

constraint diffn(x, y, w, h);

solve satisfy;

output ["ENUMSOL: x=" ++ show(x) ++ " y=" ++ show(y) ++ "\n"];
