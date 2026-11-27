% array_int_minimum and array_int_maximum shapes (issue #1006). A
% single-element array, indexed from 5, which the standard library answers
% with the element itself; arrays mixing constants with variables, one with a
% variable repeated; and the minimum and maximum of an array indexed from 0.
% The builtins are only reached for three elements or more, and only because
% Glasgow's redefinitions-2.0.mzn replaces the standard library's, which
% decomposes them into chains of int_min and int_max.
array[5..5] of var -1..1: one;
array[0..3] of var -2..2: xs;
var int: a;
var int: b;
var int: c;
var int: d;
var int: e;

constraint a = min(one);
constraint b = max(one);
constraint c = min([xs[0], 1, xs[1], -1]);
constraint d = max([xs[2], xs[2], xs[3], 0]);
constraint e = max(xs) - min(xs);
constraint xs[0] < xs[1] /\ xs[2] < xs[3];

solve satisfy;

output ["ENUMSOL: \(one) \(xs) \(a) \(b) \(c) \(d) \(e)"];
