% int_min and int_max shapes (issue #1006): a constant operand on either side,
% the same variable twice, a result that is one of its own operands, and a
% view as an operand.
var -3..3: x;
var -2..2: y;
var int: a;
var int: b;
var int: c;
var int: d;
var int: e;

constraint a = min(x, 1);
constraint b = max(-1, y);
constraint c = max(x, x);
constraint min(x, y) = y;
constraint d = max(x, y);
constraint e = min(-x, y);

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(a) \(b) \(c) \(d) \(e)"];
