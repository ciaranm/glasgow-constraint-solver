% Issue #1153: AllEqual used to disable itself as soon as its first variable
% was fixed, even when that happened part-way through a call while the others
% still held other values, and then reported solutions that violate it. Here
% the holes come from search: x1 != z0 punches one into x1 once z0 is fixed.
% The model has 8 solutions; the bug gave 9, including [2, 2, 1]. It needs this
% branching (`indomain` is smallest-value-first in the Glasgow front end).
include "globals.mzn";

var 1..5: x0;
var 0..4: x1;
var 0..5: z0;

constraint x1 != z0;
constraint x0 + z0 <= 4;
constraint x1 + z0 <= 7;
constraint all_equal([x1, x0]);

solve :: int_search([z0, x0, x1], input_order, indomain) satisfy;
output ["ENUMSOL: " ++ show([z0, x0, x1])];
