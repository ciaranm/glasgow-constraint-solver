% Minimising over a model with no solutions (issue #1006), where the objective
% is a sum the model also constrains: x + y = 0 makes x * y = -x * x, which is
% never 2.
var -3..3: x;
var -3..3: y;

constraint x * y = 2 /\ x + y = 0;

solve minimize x + y;

output ["OPTSOL: \(x + y)"];
