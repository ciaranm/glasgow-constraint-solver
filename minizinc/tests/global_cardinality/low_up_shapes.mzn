include "globals.mzn";

% The low/up forms, which the redefinitions turn into the counts forms by giving
% each cover value a count over 0..length(x) bounded by lbound and ubound: zero
% bounds, which forbid a value; an ubound past length(x); bounds and cover
% indexed from 0; the four-argument global_cardinality spelling with negative
% cover values and one outside every domain whose lbound is 0; the closed form
% with a repeated variable and an integer literal; and the closed four-argument
% form over an enum. An empty x never reaches the builtin. A negative lbound is
% in low_up_negative.mzn, which MiniZinc's default solver gets wrong.
array[1..3] of var 1..3: xa;
constraint global_cardinality_low_up(xa, array1d(0..2, [1, 2, 3]),
    array1d(0..2, [0, 0, 1]), array1d(0..2, [5, 0, 1]));

array[1..3] of var -2..-1: xb;
constraint global_cardinality(xb, [-2, 9, -1], [1, 0, 0], [2, 3, 3]);

var 1..3: a;
var 1..3: b;
constraint global_cardinality_low_up_closed([a, 2, a, b], [1, 2, 3], [0, 1, 1], [2, 2, 2]);

array[1..0] of var 1..3: x0;
constraint global_cardinality_closed(x0, [1, 2], [0, -1], [0, 2]);

enum Col = {R, G, B};
array[1..3] of var Col: xe;
constraint global_cardinality_closed(xe, [R, B], [1, 1], [1, 3]);

solve satisfy;
output ["ENUMSOL: \(xa) \(xb) \(a) \(b) \(xe)"];
