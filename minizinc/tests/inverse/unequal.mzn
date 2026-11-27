include "globals.mzn";

% Arrays of different lengths cannot be inverse, and the redefinition says so
% directly rather than handing Inverse a mismatched pair. MiniZinc's default
% solver reports `Int::channel: Sizes of argument arrays mismatch` instead, so
% the test compares against the standard library's decomposition alone. The
% flattener sees the `false` and never runs a solver, so there is no proof to
% check either.
array[1..2] of var 1..3: f;
array[1..3] of var 1..2: g;

constraint inverse(f, g);

solve satisfy;

output ["ENUMSOL: \(f) \(g)"];
