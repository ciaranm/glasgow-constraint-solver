include "table.mzn";

% A table with no rows, which nothing satisfies (#1006). The flattened table
% is an empty array, so fzn-glasgow has to post a table with no tuples rather
% than skip it.
array[1..3] of var 1..3: x;
constraint table(x, array2d(1..0, 1..3, []));

solve satisfy;
output ["ENUMSOL: \(x)"];
