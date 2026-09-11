include "globals.mzn";

% A cover that repeats a value. MiniZinc's global_cardinality says only that
% counts[i] is the number of occurrences of cover[i], so [1, 2, 1] is a legal
% model in which c[1] and c[3] are both the number of 1s. The solver's own
% GlobalCardinality requires a distinct cover, so the front end folds the repeat
% out and posts c[1] = c[3] in its place (#922). Before that, both propagators
% double-counted the demand for the repeated value: this model returned one
% solution out of 27, and the proof of the rest was rejected by VeriPB.
array[1..3] of var 1..3: x;
array[1..3] of var 0..3: c;

constraint global_cardinality(x, [1, 2, 1], c);

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(c)];
