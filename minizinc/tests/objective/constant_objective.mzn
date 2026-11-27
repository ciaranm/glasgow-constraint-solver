% A constant objective (issue #1006). The flattener does not drop it: it
% introduces a variable fixed to 3 and asks the solver to minimise that, so
% every solution is optimal. The output prints x + y, which the model fixes,
% since which solution is reported is the solver's choice.
var -3..3: x;
var -3..3: y;

constraint x + y = 1;

solve minimize 3;

output ["OPTSOL: \(x + y)"];
