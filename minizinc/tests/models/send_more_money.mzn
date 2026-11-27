% SEND + MORE = MONEY, the classic cryptarithm: one solution, 9567 + 1085 =
% 10652. Variety for the linear family (issue #1006): one equation over eight
% variables whose coefficients run from 1 to 10000 with both signs, beside an
% all_different.
include "globals.mzn";

var 0..9: S;
var 0..9: E;
var 0..9: N;
var 0..9: D;
var 0..9: M;
var 0..9: O;
var 0..9: R;
var 0..9: Y;

constraint all_different([S, E, N, D, M, O, R, Y]);
constraint S != 0 /\ M != 0;
constraint 1000 * S + 100 * E + 10 * N + D + 1000 * M + 100 * O + 10 * R + E
    = 10000 * M + 1000 * O + 100 * N + 10 * E + Y;

solve satisfy;

output ["ENUMSOL: \([S, E, N, D, M, O, R, Y])"];
