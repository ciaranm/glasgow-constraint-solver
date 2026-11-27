% `x - x <= -1`, called directly so the flattener passes it through (issue
% #1006). The two-term recovery reads it as LessThanEqual{x, x + -1}, which is
% unsatisfiable; a recovery that dropped or misplaced the constant, or swapped
% the operands, would find solutions.
var -3..3: x;

constraint int_lin_le([1, -1], [x, x], -1);

solve satisfy;

output ["ENUMSOL: \(x)"];
