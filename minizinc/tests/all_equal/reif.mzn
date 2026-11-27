include "globals.mzn";

% all_equal in a reified, half-reified and negated context, which reach the
% stdlib's fzn_all_equal_int_reif decomposition and have to flatten for us and
% agree. None of them reaches the builtin.
array[1..3] of var 0..2: x;
array[1..2] of var bool: b;

constraint b[1] <-> all_equal(x);
constraint b[2] -> all_equal([x[1], x[2]]);
constraint not all_equal([x[2], x[3], 1]);

solve satisfy;

output ["ENUMSOL: \(x) \(b)"];
