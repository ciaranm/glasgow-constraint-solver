include "globals.mzn";

% The exception set is a parameter the front end has to read: here it is empty,
% has two ranges with a hole between them and a negative value, lies entirely
% outside the variables' domains, and is hit by integer literals in the array,
% which may repeat because they are in it, beside one that is not in it and so
% rules its value out for the variables. all_different_except_0 reaches the
% same builtin by a different route, through the stdlib's alldifferent_except,
% and is over a domain on both sides of zero. The empty array is last.
array[1..2] of var 0..1: x;
array[1..2] of var {-1, 0, 2}: y;
array[1..2] of var 1..2: z;
var 0..2: a;
var 0..2: b;
array[-1..0] of var -1..0: w;
array[1..0] of var 0..2: e;

constraint all_different_except(x, {});
constraint all_different_except(y, {-1, 2});
constraint all_different_except(z, {7, 9});
constraint all_different_except([a, 0, b, 0, 1], {0});
constraint all_different_except_0(w);
constraint all_different_except(e, {1});

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(z) \(a) \(b) \(w)"];
