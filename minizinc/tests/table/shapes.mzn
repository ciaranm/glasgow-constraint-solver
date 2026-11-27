include "table.mzn";

% The shapes a front end can misread for an integer table (#1006). The
% redefinition hands glasgow_table_int the scope and the table flattened row by
% row, and fzn-glasgow cuts that back into rows of the scope's length, so every
% shape here depends on the two agreeing about what a row is.

% A single row, which pins every variable.
array[1..3] of var 0..3: a;
constraint table(a, [| 1, 0, 3 |]);

% Index sets not starting at 1, on the scope and on both of the table's
% dimensions, and negative values, some of them outside the scope's domains
% (rows 3 and 4 can never match).
array[-2..0] of var -3..1: b;
constraint table(b, array2d(5..8, -2..0, [
    -3,  0,  1,
    -1, -1, -1,
    -5,  0,  0,
     1,  2, -3]));

% A variable repeated within the scope, so that a row which gives it two
% different values cannot match.
var 1..3: c1;
var 1..3: c2;
constraint table([c1, c2, c1], [| 1, 2, 1 | 2, 2, 3 | 3, 1, 3 | 2, 3, 2 |]);

% Constants in the scope, which some rows do not match.
var 1..4: d1;
var 1..4: d2;
constraint table([d1, 2, d2, 5],
    [| 1, 2, 3, 5 | 4, 2, 1, 5 | 3, 3, 3, 5 | 2, 2, 2, 4 |]);

% An enum-indexed scope.
enum Col = {L, M, R};
array[Col] of var 1..2: e;
constraint table(e, array2d(1..2, Col, [1, 2, 1, 2, 2, 2]));

solve satisfy;
output ["ENUMSOL: \(a) \(b) \(c1) \(c2) \(d1) \(d2) \(e)"];
