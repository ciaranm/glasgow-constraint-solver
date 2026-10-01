include "globals.mzn";

% The standard library gives decreasing and strictly_decreasing no overload for a
% plain int or enum array, so without redefinitions.mzn's overloads these shapes
% are decomposed into int_lin_le and never reach the propagator (#1146): an int
% array, an enum-typed array, an array of int expressions, integer literals mixed
% in with the variables, and a two-dimensional array indexed from negative
% values. The Boolean shape reaches glasgow_increasing_bool through the standard
% library's own overload either way, and is here so that it stays there.
array[1..2] of var 1..2: a;
enum Colour = {Red, Green};
array[1..2] of var Colour: c;
var 0..1: x;
var 0..1: y;
var 1..2: m;
var 1..2: n;
array[-1..0, 3..3] of var 1..2: g;
array[1..3] of var 1..3: s;
enum Size = {Small, Medium, Large};
array[1..2] of var Size: z;
array[1..2] of var bool: b;

constraint decreasing(a);
constraint decreasing(c);
constraint decreasing([x + 1, 2 * y]);
constraint decreasing([m, 2, n]);
constraint decreasing(g);
constraint strictly_decreasing(s);
constraint strictly_decreasing(z);
constraint decreasing(b);

solve satisfy;

output ["ENUMSOL: \(a) \(c) \(x) \(y) \(m) \(n) \(g) \(s) \(z) \(b)"];
