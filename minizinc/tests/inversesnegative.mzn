include "globals.mzn";

% As inversesshapes, over the shapes that MiniZinc's default solver gets wrong,
% which is why the test compares against the standard library's decomposition
% alone. Gecode's own inverse reports `Int::channel: Number out of limits` on an
% index set holding negative values -- here f is indexed from -3 and g from 10,
% and a single element at -4 is the inverse of one at 3 -- and calls two empty
% arrays unsatisfiable, where they are trivially inverse. The empty pair never
% reaches the builtin: the redefinition guards it, because min of an empty index
% set is undefined.
array[-3..-1] of var 9..13: f;
array[10..12] of var -4..0: g;
array[-4..-4] of var -5..5: f1;
array[3..3] of var -5..5: g1;
array[1..0] of var 1..3: f0;
array[1..0] of var 1..3: g0;

constraint inverse(f, g);
constraint inverse(f1, g1);
constraint inverse(f0, g0);

solve satisfy;

output ["ENUMSOL: \(f) \(g) \(f1) \(g1)"];
