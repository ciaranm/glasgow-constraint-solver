% Maximising an objective built from a Boolean (issue #1006): bool2int(b) - x,
% where b is reified on a square, so the objective is defined through
% bool2int, int_times and int_lin_eq.
var -3..3: x;
var bool: b;

constraint b <-> x * x > 4;

solve maximize bool2int(b) - x;

output ["OPTSOL: \(bool2int(b) - x)"];
