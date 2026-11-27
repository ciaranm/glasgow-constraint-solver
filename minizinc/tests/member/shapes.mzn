include "globals.mzn";

% The shapes a front end hands member over integers (#1006): a single element
% indexed from 0; integer literals among the variables, one of them negative,
% with the searched-for value's domain reaching past every value in the array;
% a constant searched-for value with a literal beside it that is not it; the
% searched-for value as one of the array's own variables, which holds whatever
% they are; a two-dimensional array indexed from negative values, over a domain
% with holes; and an enum-typed array searched for an enum constant.
array[0..0] of var 0..1: s;
var -2..1: ys;
var {-1, 1}: a;
var -2..3: y;
var -1..1: b;
var 1..2: y2;
var 1..2: d;
array[-1..0, 2..3] of var {-4, 0, 3}: g;
enum Colour = {Red, Green, Blue};
array[Colour] of var Colour: col;

constraint member(s, ys);
constraint member([a, 2, -1], y);
constraint member([b, -1], 0);
constraint member([y2, d], y2);
constraint member(g, 3) /\ forall (i in -1..0) (g[i, 2] = -4) /\ g[0, 3] != 0;
constraint member(col, Green) /\ col[Green] = Red /\ col[Red] != Red /\ col[Blue] = Blue;

solve satisfy;

output ["ENUMSOL: \(s) \(ys) \(a) \(y) \(b) \(y2) \(d) \(g) \(col)"];
