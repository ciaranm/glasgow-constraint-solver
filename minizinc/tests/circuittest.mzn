include "globals.mzn";

% Indexed from 0 on purpose: the FlatZinc circuit predicate is defined over
% index_set(x) with successor values in that same set, so a 0-based array must
% not be shifted as if it were 1-based (regression test for the off-by-one that
% turned satisfiable 0-based circuits into spurious UNSAT).
array[0..3] of var 0..3: succ;

constraint circuit(succ);

solve satisfy;

output ["ENUMSOL: " ++ show(succ)];
