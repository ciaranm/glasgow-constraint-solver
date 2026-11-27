include "globals.mzn";

% As shapes.mzn, for global_cardinality_closed, where every entry of x must take
% a cover value, so reading the cover wrongly also changes which values x may
% take: a cover indexed from 0 with negative values, one outside every domain,
% over an x whose domain reaches past the cover; a two-dimensional x with a
% variable repeated and an integer literal that is in the cover; and an
% enum-typed x and cover. An empty x never reaches the builtin.
array[1..3] of var -3..0: xa;
array[0..2] of var 0..3: ca;
constraint global_cardinality_closed(xa, array1d(0..2, [-1, -5, -3]), ca);
constraint ca[0] >= 1;

var 1..4: a;
var 1..4: b;
array[1..3] of var 0..5: cb;
constraint global_cardinality_closed(array2d(1..2, 1..2, [a, 2, b, a]), [4, 2, 1], cb);

array[1..0] of var 1..3: x0;
array[1..2] of var 0..1: cc;
constraint global_cardinality_closed(x0, [1, 2], cc);

enum Col = {R, G, B};
array[1..3] of var Col: xe;
array[1..2] of var 0..3: ce;
constraint global_cardinality_closed(xe, [G, B], ce);
constraint ce[1] = 2;

solve satisfy;
output ["ENUMSOL: \(xa) \(ca) \(a) \(b) \(cb) \(cc) \(xe) \(ce)"];
