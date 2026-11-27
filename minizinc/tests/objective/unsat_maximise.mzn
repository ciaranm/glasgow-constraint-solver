% Maximising over a model with no solutions (issue #1006): 7 is prime and
% outside the product of two factors in -3..3, which only search shows, so the
% solver has to report UNSATISFIABLE for an optimisation problem.
var -3..3: x;
var -3..3: y;

constraint x * y = 7;

solve maximize x - y;

output ["OPTSOL: \(x - y)"];
