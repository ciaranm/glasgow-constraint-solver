include "globals.mzn";

% Not indexed from 1, on purpose: symmetric_all_different is an involution on
% the array's own index set, so the start has to reach the solver from the
% model rather than being assumed (regression test for issue #987, which
% enforced the 1-based involution here and returned a wrong UNSATISFIABLE for x,
% and wrong solutions for y). y's domain also reaches past its index set on both
% sides.
array[0..3] of var 0..3: x;
array[2..5] of var 1..6: y;

constraint symmetric_all_different(x);
constraint symmetric_all_different(y);

solve satisfy;

output ["ENUMSOL: " ++ show(x) ++ " " ++ show(y)];
