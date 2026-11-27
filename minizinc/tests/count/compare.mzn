include "globals.mzn";

% Every comparison form of count, with a variable counted value and a variable
% count, over one array with a negative literal in it. Each form is rewritten
% by its redefinition into glasgow_count_eq on a fresh count and a comparison,
% so a comparison turned round, or a fresh count without 0 in its domain, shows
% here as a different solution set. The counts range over -1..2 so that every
% form has room on both sides of the number of occurrences, which runs from 0
% (y = -2, a = -1) to 2.
var -2..-1: a;
var {-2, -1}: y;
array[1..6] of var -1..2: c;

constraint count_eq([a, -1], y, c[1]);
constraint count_geq([a, -1], y, c[2]);
constraint count_gt([a, -1], y, c[3]);
constraint count_leq([a, -1], y, c[4]);
constraint count_lt([a, -1], y, c[5]);
constraint count_neq([a, -1], y, c[6]);

solve satisfy;

output ["ENUMSOL: \(a) \(y) \(c)"];
