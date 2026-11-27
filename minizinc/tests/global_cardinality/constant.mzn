include "globals.mzn";

% A par entry in the variable array, which the front end posts as a constant in
% GlobalCardinality's scope. Before #1046 was fixed, the Hall reasoning's
% at-least-one asked the proof tracker for a constant's line, which it does not
% have, so a run with proofs aborted. Without proofs the answers were right.
var 2..3: a;
var 2..3: b;
var 0..2: d;
var 0..1: c0; var 0..1: c1; var 0..2: c2; var 0..1: c3; var 0..1: c4;

constraint global_cardinality([a, 1, b, d], [0, 1, 2, 3, 4], [c0, c1, c2, c3, c4]);

solve satisfy;
output ["ENUMSOL: " ++ show([a, b, d]) ++ " " ++ show([c0, c1, c2, c3, c4])];
