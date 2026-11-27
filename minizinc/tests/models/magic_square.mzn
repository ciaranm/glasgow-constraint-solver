% The 3 x 3 magic square: eight solutions, the rotations and reflections of the
% Lo Shu square. Variety (issue #1006): eight equal-sum rows over a 2d array,
% beside an all_different.
include "globals.mzn";

int: n = 3;
int: s = n * (n * n + 1) div 2;
array[1..n, 1..n] of var 1..n * n: m;

constraint all_different(array1d(m));
constraint forall (i in 1..n) (sum (j in 1..n) (m[i, j]) = s);
constraint forall (j in 1..n) (sum (i in 1..n) (m[i, j]) = s);
constraint sum (i in 1..n) (m[i, i]) = s;
constraint sum (i in 1..n) (m[i, n + 1 - i]) = s;

solve satisfy;

output ["ENUMSOL: \(m)"];
