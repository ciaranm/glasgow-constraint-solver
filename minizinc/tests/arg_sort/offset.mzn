include "globals.mzn";

% arg_sort's p is always indexed from 1, but its values are indices of x, so it
% is x's index set that has to reach the solver (regression test for issue
% #987, which assumed 1 and returned a wrong UNSATISFIABLE here).
array[0..2] of var 0..3: x;
array[1..3] of var 0..2: p;

constraint arg_sort(x, p);

solve satisfy;

output ["ENUMSOL: " ++ show(x) ++ " " ++ show(p)];
