include "globals.mzn";

% No rectangles at all, for both forms (#1006): neither wrapper guards an
% empty array, so each reaches its builtin with four empty arrays. Native
% Gecode's diffn reports =====ERROR===== on it, so this has its own model.
array[1..0] of var 0..1: none;
var 0..2: z;

constraint diffn(none, none, none, none);
constraint diffn_nonstrict(none, none, none, none);

solve satisfy;

output ["ENUMSOL: \(z)"];
