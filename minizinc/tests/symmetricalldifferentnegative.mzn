include "globals.mzn";

% As symmetricalldifferentshapes, over the shapes that MiniZinc's default solver
% gets wrong, which is why the test compares against the standard library's
% decomposition alone. Gecode's own symmetric_all_different reports
% `Int::channel: Number out of limits` on an index set holding negative values,
% here one from -1 and a single element at -4, and calls it unsatisfiable when
% the array is empty, where the involution holds trivially. The empty array
% never reaches the builtin: the redefinition guards it, because min of an empty
% index set is undefined.
array[-1..1] of var -2..2: neg;
array[-4..-4] of var -5..5: one;
array[1..0] of var 1..3: empty;

constraint symmetric_all_different(neg);
constraint symmetric_all_different(one);
constraint symmetric_all_different(empty);

solve satisfy;

output ["ENUMSOL: \(neg) \(one) \(empty)"];
