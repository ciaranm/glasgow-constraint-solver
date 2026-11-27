% Maximising a variable whose domain is wholly negative and has holes (issue
% #1006), so the objective is a model variable itself. The optimum, -5, is
% below a value the domain allows, because x mod 3 = -1 (truncating) rules out
% -2 for x.
var {-9, -7, -6, -4, -2}: x;
var -9..-1: y;

constraint x mod 3 = -1 \/ x = -9;
constraint y < x;

solve maximize y;

output ["OPTSOL: \(y)"];
