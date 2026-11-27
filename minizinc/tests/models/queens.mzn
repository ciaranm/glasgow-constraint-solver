% Six queens, the classic: four solutions. Variety (issue #1006): three
% all_different constraints, two of them over arrays of introduced variables
% offset from the queens by a two-term int_lin_eq each.
include "globals.mzn";

int: n = 6;
array[1..n] of var 1..n: q;

constraint all_different(q);
constraint all_different([q[i] + i | i in 1..n]);
constraint all_different([q[i] - i | i in 1..n]);

solve satisfy;

output ["ENUMSOL: \(q)"];
