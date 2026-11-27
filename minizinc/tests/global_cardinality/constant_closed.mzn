include "globals.mzn";

% The closed form with a par entry, posted as a constant in the scope. Before
% #1046 was fixed, the bounds arm's demand reasoning gave the constant an
% at-most-one over its atoms, two of which are false, and recover_am1's short cut
% for two false atoms then wrote a bare `0 >= 1` RUP that VeriPB rejected.
var 1..3: a;
var 1..4: b;
var 0..1: c0; var 0..1: c1; var 0..2: c2; var 0..1: c3; var 0..1: c4;

constraint global_cardinality_closed([a, b, 0], [0, 1, 2, 3, 4], [c0, c1, c2, c3, c4]);

solve satisfy;
output ["ENUMSOL: " ++ show([a, b]) ++ " " ++ show([c0, c1, c2, c3, c4])];
