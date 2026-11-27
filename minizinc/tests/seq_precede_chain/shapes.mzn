include "globals.mzn";

% The shapes a front end can misread for seq_precede_chain (#1006), each of
% which reaches the builtin: an x indexed from 0 whose domain has negative
% values and zero, which the constraint leaves free; an empty x; a single
% element indexed from 5; integer literals and a repeated variable; and a
% domain with a hole at 1, so no positive value can occur.
array[0..2] of var -1..2: xa;
constraint seq_precede_chain(xa);
constraint xa[0] != 0 /\ xa[1] = xa[2];

array[1..0] of var 1..3: x0;
constraint seq_precede_chain(x0);

array[5..5] of var 0..3: x1;
constraint seq_precede_chain(x1);

var 0..3: a;
var 1..3: b;
constraint seq_precede_chain([a, 2, b, a]);

array[-2..-1] of var {-3, 0, 2, 3}: xe;
constraint seq_precede_chain(xe);
constraint xe[-2] = 0;

solve satisfy;
output ["ENUMSOL: \(xa) \(x1) \(a) \(b) \(xe)"];
