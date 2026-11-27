include "globals.mzn";

% The Boolean builtins, plain and reified (#1006): arrays of unequal length
% indexed from 0 and -2; a Boolean literal on each side; a reified, a
% half-reified and a negated call, each of which reaches a _reif builtin; and an
% empty array, which never reaches one.
array[0..1] of var bool: x;
array[-2..0] of var bool: y;
var bool: r1;
var bool: r2;
var bool: r3;
constraint lex_less(x, y);
constraint lex_lesseq([true, y[-1]], x);
constraint r1 <-> lex_less(y, x);
constraint r2 -> lex_lesseq(x, y);
constraint not lex_less(y, [x[0], false]) \/ r3;

array[1..0] of var bool: e;
constraint lex_less(e, x);

solve satisfy;
output ["ENUMSOL: \(x) \(y) \(r1) \(r2) \(r3)"];
