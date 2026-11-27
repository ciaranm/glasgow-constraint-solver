include "table.mzn";

% The Boolean table's shapes (#1006): a single row; a variable repeated
% within the scope alongside a constant; and a scope indexed from 3 with a
% table whose rows are indexed from 0.
array[1..2] of var bool: a;
constraint table(a, [| true, false |]);

var bool: p;
var bool: q;
constraint table([p, q, p, true], [|
    true,  false, true,  true  |
    false, false, true,  true  |
    false, true,  false, true  |
    true,  true,  true,  false |]);

array[3..5] of var bool: c;
constraint table(c, array2d(0..2, 3..5, [
    true,  true,  false,
    false, false, false,
    true,  false, true]));

solve satisfy;
output ["ENUMSOL: \(a) \(p) \(q) \(c)"];
