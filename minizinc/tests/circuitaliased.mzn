include "globals.mzn";

% Equating two entries makes MiniZinc give them one FlatZinc variable, so
% circuit sees the same variable twice in one array. That is unsatisfiable,
% and used to be rejected with an error instead of answered (#1047).
array[1..3] of var 1..3: f;

constraint f[1] = f[2];
constraint circuit(f);

solve satisfy;

output ["ENUMSOL: \(f)"];
