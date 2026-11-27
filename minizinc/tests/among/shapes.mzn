include "globals.mzn";

% The shapes a front end hands among (#1006): an empty array; a single element
% indexed from 5 with a negative value set; integer literals among the
% variables, one in the value set and one not, against a set with negative
% values and two holes, which is three ranges in the JSON and whose hull would
% take in values the variables can have; an empty value set; and an
% enum-typed array, whose value set {Red, Blue} has a hole at Green, with a
% constant count. The last is a bool array with a literal in it, which MiniZinc
% coerces to integers.
array[1..0] of var 1..3: e;
var 0..1: ne;
array[5..5] of var -2..0: s;
var 0..1: ns;
var -3..1: a;
var {-1, 5}: b;
var -1..4: n;
array[1..1] of var 0..1: d;
var 0..1: nd;
enum Colour = {Red, Green, Blue};
array[-1..0] of var Colour: col;
var bool: p;
var bool: q;

constraint among(ne, e, {1, 2});
constraint among(ns, s, {-1});
constraint among(n, [a, b, -3, 4], {-3, 0, 1, 5});
constraint among(nd, d, {});
constraint among(1, col, {Red, Blue}) /\ col[0] = Green;
constraint among(1, [p, q, false], {1});

solve satisfy;

output ["ENUMSOL: \(ne) \(s) \(ns) \(a) \(b) \(n) \(d) \(nd) \(col) \(p) \(q)"];
