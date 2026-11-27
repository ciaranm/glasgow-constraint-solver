% int_lt called directly on one variable twice, which the flattener passes
% through (issue #1006): unsatisfiable, and a front end that posted
% LessThanEqual for it, or a propagator that assumed distinct operands, would
% find solutions.
var -2..2: x;

constraint int_lt(x, x);

solve satisfy;

output ["ENUMSOL: \(x)"];
