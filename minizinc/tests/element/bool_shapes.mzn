% Element on Boolean arrays (#1006): a parameter array indexed from 0 and an
% array of variables indexed from -1, each with an index variable whose domain
% reaches past it. The first two sit inside a Boolean expression rather than
% at the top level, so MiniZinc keeps the out-of-range indices and makes the
% expression false on them; the third is a constraint by itself, where
% MiniZinc cuts the index's domain to the index set instead.
array[0..3] of bool: pb = array1d(0..3, [true, false, false, true]);
var -1..5: i;
var bool: b;
constraint b = pb[i];

array[-1..1] of var bool: vb;
var -2..2: j;
constraint vb[j] != vb[-1];

var -1..5: m;
constraint pb[m];

solve satisfy;
output ["ENUMSOL: \(i) \(b) \(vb) \(j) \(m)"];
