include "table.mzn";

% As empty.mzn, for the Boolean table, which has a redefinition of its own.
array[1..2] of var bool: x;
constraint table(x, array2d(1..0, 1..2, []));

solve satisfy;
output ["ENUMSOL: \(x)"];
