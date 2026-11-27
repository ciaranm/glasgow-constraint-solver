include "globals.mzn";

% The shapes a front end can misread for global_cardinality (#1006), each of
% which reaches the builtin: a cover with negative values and one value outside
% every domain, whose count must be 0; a cover and counts indexed from -1 over a
% two-dimensional x indexed from 0, which the stdlib's wrapper flattens; an empty
% cover and counts, which says nothing; a variable repeated in x alongside
% integer literals, one of which is outside the cover and must not be counted;
% and an enum-typed x and cover. An empty x never reaches the builtin, since the
% wrapper fixes its counts at 0 itself, but is here so that it stays that way.
array[1..3] of var -2..0: xa;
array[1..3] of var 0..3: ca;
constraint global_cardinality(xa, [-2, 7, -1], ca);
constraint ca[1] = 1;
constraint xa[1] < xa[2];

array[0..1, 3..4] of var 1..2: xb;
array[-1..0] of var 0..4: cb;
constraint global_cardinality(xb, array1d(-1..0, [2, 1]), cb);
constraint global_cardinality(xb, [], []);
constraint cb[-1] = 3;

var 1..3: a;
var 1..3: b;
array[1..3] of var 0..4: cc;
constraint global_cardinality([a, 5, a, b, 1], [1, 2, 3], cc);
constraint cc[1] = 3;

array[1..0] of var 1..3: x0;
array[1..2] of var 0..1: cd;
constraint global_cardinality(x0, [1, 2], cd);

enum Col = {R, G, B};
array[1..2] of var Col: xe;
array[1..2] of var 0..2: ce;
constraint global_cardinality(xe, [B, R], ce);
constraint ce[1] = 1;

solve satisfy;
output ["ENUMSOL: \(xa) \(ca) \(xb) \(cb) \(a) \(b) \(cc) \(cd) \(xe) \(ce)"];
