% Element on arrays of variables not indexed from 1 (#1006), with the result
% aliased with something the element constraint also mentions.

% An array indexed from -1, whose index variable's domain reaches past both
% ends of it, and whose result is the index itself (which MiniZinc's shift
% turns into a different variable from the one the builtin indexes by).
array[-1..0] of var -1..0: x;
var -4..3: i;
constraint x[i] = i;

% An array indexed from 3, whose result is one of its own entries.
array[3..4] of var 1..2: y;
var 2..6: j;
constraint y[j] = y[3];

% A 1-based array, so that the builtin gets the very same variable as its
% index and its result.
array[1..2] of var 1..2: z;
var 0..3: k;
constraint z[k] = k;

solve satisfy;
output ["ENUMSOL: \(x) \(i) \(y) \(j) \(z) \(k)"];
