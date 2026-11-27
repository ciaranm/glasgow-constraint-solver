include "globals.mzn";

% all_different reads no index set, so what a front end can get wrong here is
% the array it is handed: an empty one, a single element indexed from 7, integer
% literals mixed in with the variables, a two-dimensional array indexed from
% negative values over a domain with holes, and an enum-typed array over an enum
% index set.
array[1..0] of var 1..3: e;
array[7..7] of var 1..2: s;
var 1..4: a;
var 1..4: b;
array[-1..0, 3..4] of var {-4, -1, 0, 5}: g;
enum Colour = {Red, Green};
enum Slot = {First, Second};
array[Slot] of var Colour: c;

constraint all_different(e);
constraint all_different(s);
constraint all_different([a, 2, b, 4]);
constraint all_different(g);
constraint g[-1, 3] < g[-1, 4] /\ g[0, 3] < g[0, 4];
constraint all_different(c);

solve satisfy;

output ["ENUMSOL: \(s) \(a) \(b) \(g) \(c)"];
