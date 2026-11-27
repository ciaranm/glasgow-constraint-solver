include "globals.mzn";

% The shapes a front end hands all_equal (#1006): an empty array and a single
% element indexed from 4, which the stdlib wrapper answers with true before any
% builtin is posted; an integer literal between two copies of one variable; a
% variable repeated beside another whose domain overlaps it; a two-dimensional
% array indexed from negative values over a domain with holes; an enum-typed
% array; and a bool array, which MiniZinc coerces to integers.
array[1..0] of var 1..3: e;
array[4..4] of var -1..0: s;
var -3..0: a;
var 1..3: c;
var 2..4: d;
array[-1..0, 5..6] of var {-3, 0, 5}: g;
enum Colour = {Red, Green, Blue};
array[Colour] of var Colour: col;
var bool: p;
var bool: q;

constraint all_equal(e);
constraint all_equal(s);
constraint all_equal([a, -2, a]);
constraint all_equal([c, c, d]);
constraint all_equal(g) /\ g[-1, 5] != 5;
constraint all_equal(col) /\ col[Red] != Red;
constraint all_equal([p, q]);

solve satisfy;

output ["ENUMSOL: \(s) \(a) \(c) \(d) \(g) \(col) \(p) \(q)"];
