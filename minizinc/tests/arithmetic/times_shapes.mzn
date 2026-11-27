% int_times shapes (issue #1006): negative factors, a variable squared, which
% hands the builtin the same variable twice, two views as factors, a product
% that equals one of its own factors, and a zero term that the flattener drops
% next to a square.
var -3..3: x;
var -2..2: y;
var int: p;
var int: q;
var int: r;
var -1..1: z;

constraint p = x * y;
constraint q = x * x;
constraint r = (-x) * (y - 1);
constraint x * z = x;
constraint 0 * y + z * z = 1;

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(p) \(q) \(r) \(z)"];
