include "globals.mzn";

% arg_sort's p is always indexed from 1, but its values are indices of x, so each
% of these reaches the builtin with an offset the front end must read off x
% (issue #1006, after #987; argsortoffset has x indexed from 0). Here: x indexed
% from -3 with p's domain reaching past that index set on both sides; x indexed
% from 100; an enum-indexed x, which the stdlib's wrapper turns into integers;
% integer literals and a repeated variable in x, whose ties the stable sort must
% break by index; the function form over a single element indexed from 7; and
% an empty x, which never reaches the builtin because the redefinition guards
% it.
%
% The single element is written with the function form on purpose. The
% predicate form, `arg_sort(x, p)` with p declared over a wider domain, is where
% the standard library's decomposition is laxer than its documentation: its
% `forall` is empty when x has one element, so nothing ties p[1] to x's index
% set, where ArgSort follows the documented "p is a permutation". The function
% form declares p over index_set(x), so the two readings agree.
array[-3..-1] of var 0..1: xn;
array[1..3] of var -4..0: pn;
array[100..101] of var 0..1: xl;
array[1..2] of var 99..102: pl;
enum Level = {Lo, Hi};
array[Level] of var 0..1: xe;
array[1..2] of var Level: pe;
var 0..1: a;
var 0..1: b;
array[1..4] of var 0..3: pc;
var 0..1: c;
array[1..0] of var 0..1: x0;
array[1..0] of var 1..3: p0;

constraint arg_sort(xn, pn);
constraint xn[-3] = 1;
constraint arg_sort(xl, pl);
constraint xl[100] >= xl[101];
constraint arg_sort(xe, pe);
constraint arg_sort(array1d(0..3, [a, 1, a, b]), pc);
array[int] of var int: ps = arg_sort(array1d(7..7, [c]));
constraint arg_sort(x0, p0);

solve satisfy;

output ["ENUMSOL: \(xn) \(pn) \(xl) \(pl) \(xe) \(pe) \(a) \(b) \(pc) \(c) \(ps)"];
