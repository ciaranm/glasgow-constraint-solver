include "globals.mzn";

% inverse in a reified and in a negated context, which reach the stdlib's
% fzn_inverse_reif decomposition and have to flatten for us and agree: over
% two arrays indexed from different places, and over one array that is its own
% inverse. None of them reaches the builtin.
array[0..1] of var 5..6: f;
array[5..6] of var 0..1: g;
array[3..4] of var 3..4: h;
array[1..2] of var bool: b;

constraint b[1] <-> inverse(f, g);
constraint not inverse(h, h) \/ b[2];

solve satisfy;

output ["ENUMSOL: \(f) \(g) \(h) \(b)"];
