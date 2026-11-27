include "globals.mzn";

% Reified, half-reified and negated increasing and strictly_increasing, over
% arrays indexed from 0 and 3, a Boolean array, and a single element. None has
% a builtin, so they reach the stdlib's reified decompositions, but the
% redefinitions must not stop them flattening. An empty array is left out: the
% stdlib's reified increasing takes the minimum of its index set, so
% `r <-> increasing([])` is unsatisfiable for every solver (redefinitions.mzn
% guards decreasing against that, but not increasing).
array[0..1] of var 1..2: y;
array[1..2] of var bool: bb;
array[1..1] of var 1..3: o;
var bool: r1;
var bool: r2;
var bool: r3;
var bool: r4;
var bool: r5;
constraint r1 <-> increasing(y);
constraint r2 -> strictly_increasing(y);
constraint r3 <-> not increasing(bb);
constraint r4 -> increasing(array1d(3..4, bb));
constraint r5 <-> strictly_increasing(o);

solve satisfy;
output ["ENUMSOL: \(y) \(bb) \(o) \(r1) \(r2) \(r3) \(r4) \(r5)"];
