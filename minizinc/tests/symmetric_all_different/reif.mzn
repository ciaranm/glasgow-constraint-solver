include "globals.mzn";

% symmetric_all_different in a reified, a half-reified and a negated context,
% which reach the stdlib's fzn_symmetric_all_different_reif decomposition and
% have to flatten for us and agree, over arrays indexed from -1 and from 3.
% None of them reaches the builtin.
array[-1..0] of var -1..0: s;
array[3..4] of var 3..4: h;
array[3..4] of var 3..4: k;
array[1..2] of var bool: b;

constraint not symmetric_all_different(s);
constraint b[1] -> symmetric_all_different(h);
constraint b[2] <-> symmetric_all_different(k);

solve satisfy;

output ["ENUMSOL: \(s) \(h) \(k) \(b)"];
