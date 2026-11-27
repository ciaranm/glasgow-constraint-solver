include "globals.mzn";

% at_least, at_most and exactly, which the stdlib still offers though they
% are deprecated, and which have redefinitions of their own. Each of the first
% four has its own array: one where a count of 0 is a solution, one with a
% negative counted value, and one with a variable repeated beside a literal,
% whose counted value nothing in the array can take. The last three are over an
% empty array, with the counts at the only value they can have, and different
% counted values so that the flattener cannot merge them into one call.
array[1..2] of var 0..1: p;
array[1..2] of var 0..1: q;
array[1..2] of var -1..0: r;
var -2..0: s;
array[1..0] of var 1..3: e;

constraint at_least(1, p, 0);
constraint at_most(1, q, 1);
constraint exactly(1, r, -1);
constraint exactly(0, [s, -1, s], -2);
constraint at_least(0, e, 1);
constraint at_most(0, e, 2);
constraint exactly(0, e, 3);

solve satisfy;

output ["ENUMSOL: \(p) \(q) \(r) \(s)"];
