include "globals.mzn";

% The shapes a front end can misread for lex_less and lex_lesseq (#1006):
% arrays of unequal length with different index sets, neither from 1; integer
% literals and a variable shared between the two sides; enum-valued arrays,
% through lex_greater; an empty array on the left against a non-empty one, and
% on both sides, which the stdlib's wrapper decides itself; the same array on
% both sides of lex_lesseq; and one element against two through the lex_lt and
% lex_leq aliases. The count is three of each builtin: the empty arrays never
% reach one, and the rest must.
array[0..1] of var 0..1: xa;
array[-1..1] of var 0..1: ya;
constraint lex_less(xa, ya);
constraint ya[-1] = xa[0] /\ ya[1] = xa[0] /\ xa[1] = 1;

var 0..1: a;
var 0..2: b;
constraint lex_lesseq([a, 1, b], [a, b]);

enum Col = {R, G, B};
array[1..2] of var Col: xc;
array[1..2] of var Col: yc;
constraint lex_greater(xc, yc);
constraint xc[1] = G /\ yc[2] != R;

array[1..0] of var 0..1: e;
array[1..2] of var 0..1: yd;
constraint lex_less(e, yd);
constraint lex_lesseq(e, e);

array[3..4] of var 0..1: xe;
constraint lex_lesseq(xe, xe);

var 0..1: f;
array[1..2] of var 0..1: yf;
constraint lex_lt([f], yf);
constraint lex_leq(yf, [1, f]);
constraint yd[1] = 1 /\ yd[2] = f;
constraint xe[3] = 0 /\ xe[4] = f;

solve satisfy;
output ["ENUMSOL: \(xa) \(ya) \(a) \(b) \(xc) \(yc) \(yd) \(xe) \(f) \(yf)"];
