include "globals.mzn";

% More shapes for arg_sort beyond shapes.mzn (#1006): a negated call over an x
% indexed from 2, which reaches the stdlib's reified decomposition rather than
% the builtin; integer literals in p as well as x, with x indexed from -1, so
% the literal 0 is an index only at the right offset; a par x indexed from 10
% with a tie, so the only p is the stable one; and an enum-valued x, which the
% wrapper sorts by the enum's order.
array[2..3] of var 0..1: xa;
array[1..2] of var 1..3: pa;
constraint not arg_sort(xa, pa);
constraint pa[1] < pa[2];

var 0..2: u;
var 0..1: v;
var -1..1: q;
var -1..1: t;
constraint arg_sort(array1d(-1..1, [u, v, 1]), [0, q, t]);

array[1..3] of var 9..13: pc;
constraint arg_sort(array1d(10..12, [5, 3, 5]), pc);

enum Col = {R, G, B};
array[1..2] of var Col: xd;
array[1..2] of var 1..2: pd;
constraint arg_sort(xd, pd);
constraint xd[1] != G;

solve satisfy;
output ["ENUMSOL: \(xa) \(pa) \(u) \(v) \(q) \(t) \(pc) \(xd) \(pd)"];
