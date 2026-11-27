include "globals.mzn";

% Variable durations: each task's length is a decision variable, exercising
% glasgow_disjunctive's variable-duration path. Strict mode (durations >= 1).
% Enumerated against MiniZinc's default solver.
int: n = 3;
array[1..n] of var 0..4: s;
array[1..n] of var 1..2: d;

constraint disjunctive_strict(s, d);

solve satisfy;

output ["ENUMSOL: s=" ++ show(s) ++ " d=" ++ show(d) ++ "\n"];
