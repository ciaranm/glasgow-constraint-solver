include "globals.mzn";

% A closed global_cardinality with an empty cover over a non-empty x, which no
% value can satisfy. The stdlib's wrapper only guards an empty x, so this
% reaches the builtin with no cover at all.
array[1..2] of var 1..2: x;
array[int] of int: cover = [];
array[int] of var int: counts = [];
constraint global_cardinality_closed(x, cover, counts);

solve satisfy;
output ["ENUMSOL: \(x)"];
