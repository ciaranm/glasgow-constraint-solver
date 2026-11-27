include "globals.mzn";

% Reified, half-reified and negated calls of all four forms, over an x indexed
% from 0. None has a builtin, so they reach the stdlib's reified
% decompositions, but the redefinitions must not stop them flattening.
array[0..2] of var 1..2: x;
array[1..2] of var 0..3: c;
var bool: r1;
var bool: r2;
var bool: r3;
var bool: r4;
constraint r1 <-> global_cardinality(x, [1, 3], c);
constraint r2 -> global_cardinality_closed(x, [2, 3], c);
constraint r3 <-> not global_cardinality_low_up(x, [1, 2], [1, 1], [2, 2]);
constraint r4 -> global_cardinality_low_up_closed(x, [1, 2], [0, 2], [1, 3]);
constraint c[1] <= 1;

solve satisfy;
output ["ENUMSOL: \(x) \(c) \(r1) \(r2) \(r3) \(r4)"];
