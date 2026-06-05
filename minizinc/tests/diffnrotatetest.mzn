include "globals.mzn";

% Rotatable rectangles: each is a 1x2 piece that may rotate to 2x1, so its
% width and height are decision variables (var dx/dy into diffn), exercising
% glasgow_diffn's variable-size path. Enumerated against the default solver.
int: n = 2;
array[1..n] of var bool: rot;
array[1..n] of var 0..2: x;
array[1..n] of var 0..2: y;
array[1..n] of var 1..2: dx = [if rot[i] then 2 else 1 endif | i in 1..n];
array[1..n] of var 1..2: dy = [if rot[i] then 1 else 2 endif | i in 1..n];

constraint diffn(x, y, dx, dy);

solve satisfy;

output ["ENUMSOL: x=" ++ show(x) ++ " y=" ++ show(y) ++ " rot=" ++ show(rot) ++ "\n"];
