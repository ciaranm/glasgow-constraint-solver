include "globals.mzn";

% The shapes a front end hands count (#1006), each reaching glasgow_count_eq
% through a different stdlib route: the function form over an empty array and
% over a single element indexed from 7, both with a constant counted value; the
% predicate form with a variable counted value over an array that mixes integer
% literals, one of them negative, with a variable that appears twice, where the
% counted value's domain also holds a value nothing in the array can take; a
% constant count over a two-dimensional array indexed from negative values; an
% enum-typed array counted by enum constants, one of them with count 0; and a
% bool array with a literal in it, which MiniZinc coerces to integers.
array[1..0] of var 1..3: e;
var 0..1: ce;
array[7..7] of var -2..-1: s;
var 0..1: cs;
var 1..2: a;
var {-1, 2, 5}: y;
var 0..5: c;
array[-1..0, 3..4] of var {-3, -1}: g;
enum Colour = {Red, Green, Blue};
array[Colour] of var Colour: col;
var bool: p;
var bool: q;

constraint count(e, 2) = ce;
constraint count(s, -1) = cs;
constraint count([a, 2, a, -1], y, c);
constraint count(g, -3) = 3;
constraint count(col, Green) = 0 /\ count(col, Blue) = 2;
constraint count([p, q, true], true) = 2;

solve satisfy;

output ["ENUMSOL: \(ce) \(s) \(cs) \(a) \(y) \(c) \(g) \(col) \(p) \(q)"];
