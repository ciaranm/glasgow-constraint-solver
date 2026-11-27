include "regular.mzn";

% Solutions are those matching the following regular expression: 11*22*11*|3*
array[1..5] of var 1..3: xs;

array[1..5, 1..3] of int: t =
[|2, 0, 5,
|2, 3, 0,
|4, 3, 0,
|4, 0, 0,
|0, 0, 5|];

constraint regular(xs, 5, 3, t, 1, 4..5);

solve satisfy;
output ["ENUMSOL: " ++ join(" ", [show(x) | x in xs])];