include "globals.mzn";

% The shapes a front end hands diffn and diffn_nonstrict (#1006), each
% reaching glasgow_diffn or glasgow_diffn_nonstrict, which the lane counts
% separately. The two differ exactly on rectangles of zero width or height,
% which diffn still keeps out of every other rectangle and diffn_nonstrict
% lets sit anywhere, so most calls here have one.
array[0..2] of var -1..0: x;
array[0..2] of var 0..1: y;
var 0..1: w;

% Strict: a zero-width and a zero-height rectangle beside a 2x1 one, at
% negative x, over an index set starting at 0.
constraint diffn(x, y, array1d(0..2, [2, 0, 1]), array1d(0..2, [1, 1, 0]));

% Non-strict: a zero-width rectangle, at the integer-literal origin x = 0,
% which may sit inside the 2x1 one when that starts at x = -1, as diffn would
% not allow; and a variable width that can be zero, at an origin repeated from
% the 2x1 one, over a negative index set. The fixed sizes are not square, so
% swapping widths and heights shows.
constraint diffn_nonstrict(array1d(-2..0, [x[0], 0, x[0]]),
    array1d(-2..0, [y[1], y[2], 1]), array1d(-2..0, [2, 0, w]),
    array1d(-2..0, [1, 2, 1]));

% Single rectangles, one of each form, with a variable size, at an index far
% from 1.
constraint diffn(array1d(10..10, [x[1]]), array1d(10..10, [y[1]]),
    array1d(10..10, [w]), array1d(10..10, [1]));
constraint diffn_nonstrict(array1d(10..10, [x[2]]), array1d(10..10, [y[2]]),
    array1d(10..10, [0]), array1d(10..10, [w]));

% A reified call, which has to reach the standard library's decomposition.
var bool: rb;
constraint rb <-> diffn([x[1], x[2]], [y[0], y[0]], [1, w], [1, 1]);

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(w) \(rb)"];
