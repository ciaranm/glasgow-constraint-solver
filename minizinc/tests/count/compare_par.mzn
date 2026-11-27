include "globals.mzn";

% The comparison forms of count again, as compare.mzn, but with a constant
% counted value and a constant count, which the stdlib routes through its
% fzn_count_*_par predicates before reaching the redefinitions. Each form has
% its own array, so that each one alone decides which assignments of it
% survive, and the arrays have literals in them, one counted and one not, and
% negative values.
array[1..2] of var 0..1: p;
array[1..2] of var 0..1: q;
array[1..2] of var -1..0: r;
array[1..2] of var -1..0: t;
var -2..0: s;

constraint count_geq(p, 1, 1);
constraint count_gt(q, 0, 2);
constraint count_leq([r[1], -1, r[2]], -1, 2);
constraint count_lt(t, 0, 1);
constraint count_neq([s, 0, 1], 0, 1);

solve satisfy;

output ["ENUMSOL: \(p) \(q) \(r) \(t) \(s)"];
