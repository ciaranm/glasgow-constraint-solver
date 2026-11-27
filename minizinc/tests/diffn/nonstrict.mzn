include "globals.mzn";

% Non-strict diffn with a width that may be 0: a zero-width rectangle is
% zero-area and does not constrain (the zero-size escape). Exercises
% glasgow_diffn_nonstrict end to end. Enumerated against the default solver.
int: n = 2;
array[1..n] of var 0..1: dx;
array[1..n] of var 1..2: dy;
array[1..n] of var 0..2: x;
array[1..n] of var 0..2: y;

constraint diffn_nonstrict(x, y, dx, dy);

solve satisfy;

output ["ENUMSOL: x=" ++ show(x) ++ " y=" ++ show(y) ++ " dx=" ++ show(dx) ++ " dy=" ++ show(dy) ++ "\n"];
