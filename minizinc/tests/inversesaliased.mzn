include "globals.mzn";

% Equating two entries makes MiniZinc give them one FlatZinc variable, so
% inverse sees the same variable twice in one array. That is unsatisfiable,
% and used to be rejected with an error instead of answered (#1047).
array[1..3] of var 1..3: f;
array[1..3] of var 1..3: g;

constraint f[1] = f[2];
constraint inverse(f, g);

solve satisfy;

output ["ENUMSOL: \(f) \(g)"];
