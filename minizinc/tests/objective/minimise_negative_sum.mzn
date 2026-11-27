% Minimising a sum over wholly negative domains (issue #1006): the objective is
% an introduced variable defined by an int_lin_eq, and the optimum, -12 at
% (-3, -9), is interior to the product constraint rather than at a bound.
var -9..-2: x;
var -9..-2: y;

constraint x * y <= 30;
constraint x != y;

solve minimize x + y;

output ["OPTSOL: \(x + y)"];
