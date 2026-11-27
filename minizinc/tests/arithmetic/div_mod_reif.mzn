% int_div and int_mod under a reification, a half-reification and with a
% divisor whose domain includes 0 (issue #1006). Here a zero divisor must not
% make the model unsatisfiable: it makes the enclosing comparison false, so
% r and s are false and t cannot hold when b = 0. The flattener gets there by
% handing the builtin a stand-in divisor that is 1 when b is 0, plus a
% definedness flag; the builtin must still read truncating division on the
% negative operands, or r and s come out wrong on the other 120 rows.
var -3..3: a;
var -2..2: b;
var -1..1: c;
var bool: r;
var bool: s;
var bool: t;

constraint r <-> (a div b = c);
constraint s <-> (a mod b = c);
constraint t -> (a div b > 0);

solve satisfy;

output ["ENUMSOL: \(a) \(b) \(c) \(r) \(s) \(t)"];
