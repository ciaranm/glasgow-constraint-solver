include "globals.mzn";

% lex_less and lex_lesseq have builtins for their reified forms, so a reified,
% half-reified or negated call reaches Glasgow, not a decomposition, and the
% counts insist on each: a reified call over arrays of unequal length with
% different index sets; a half-reified call with the sides swapped; a reified
% negation against an integer literal; and a half-reified negation of a single
% element against two. An empty array on either side never reaches a builtin,
% since the stdlib's wrapper decides it, and is here so that it stays that way.
array[0..1] of var 0..1: x;
array[1..3] of var 0..1: y;
var bool: r1;
var bool: r2;
var bool: r3;
var bool: r4;
constraint r1 <-> lex_less(x, y);
constraint r2 -> lex_lesseq(y, x);
constraint r3 <-> not lex_lesseq(x, [1, y[2]]);
constraint r4 -> not lex_less([y[1]], x);

array[1..0] of var 0..1: e;
var bool: r5;
var bool: r6;
constraint r5 <-> lex_less(x, e);
constraint r6 <-> lex_lesseq(e, y);

solve satisfy;
output ["ENUMSOL: \(x) \(y) \(r1) \(r2) \(r3) \(r4) \(r5) \(r6)"];
