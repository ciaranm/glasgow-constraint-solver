include "globals.mzn";

% how_many is the value of interest, and the bound the propagator pushes on
% how_many also prunes the value of interest, so the array pruning after it
% has to look at the state after that push. It used to prune a != 1 and report
% no solutions (issue #1304).
var 1..6: y;
var 0..1: a;
var 3..4: b;
var 5..6: c;

constraint count([4, a, b, c], y) = y;

solve satisfy;
output ["ENUMSOL: " ++ show([y, a, b, c])];
