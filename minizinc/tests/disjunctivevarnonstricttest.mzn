include "globals.mzn";

% Variable durations including zero, non-strict mode: a task whose duration
% takes the value 0 floats freely (the zero-length escape), while positive
% durations must not overlap. Exercises glasgow_disjunctive's variable-duration
% non-strict path. Enumerated against MiniZinc's default solver.
int: n = 3;
array[1..n] of var 0..3: s;
array[1..n] of var 0..2: d;

constraint disjunctive(s, d);

solve satisfy;

output ["ENUMSOL: s=" ++ show(s) ++ " d=" ++ show(d) ++ "\n"];
