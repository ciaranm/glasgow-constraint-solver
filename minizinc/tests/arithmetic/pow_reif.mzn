% int_pow under a reification and a half-reification (issue #1006), where a
% zero base with a negative exponent makes the comparison false rather than
% the model unsatisfiable. The flattener hands the builtin a stand-in base that
% is 1 in that case; b must still be false there. d is a constant negative
% exponent in a reified context, which goes through int_div instead, and
% agrees with the builtin on every row.
var -2..2: x;
var -2..2: y;
var -4..4: z;
var bool: b;
var bool: c;
var bool: d;

constraint b <-> (pow(x, y) = z);
constraint c -> (pow(x, y) > 1);
constraint d <-> (pow(x, -1) = z);

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(z) \(b) \(c) \(d)"];
