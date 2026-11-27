include "mdd.mzn";

% The shapes fzn-glasgow's mdd translation can misread (#1006). MiniZinc
% numbers the nodes 1..N with a level for each, and node 0 is the true
% terminal; fzn-glasgow regroups the nodes by level and renumbers them within
% each, which the shapes below depend on. (An x not indexed from 1 is out of
% scope: the standard library's own decomposition reads x by level.)

% Nodes numbered out of level order (2 is on level 3, 3 and 4 on level 2), a
% node that nothing reaches (6), a dead end (5), an edge with an empty label,
% labels with holes and negative values, and values of x that no edge carries.
array[1..3] of var -2..2: a;
constraint mdd(a, 6, [1, 3, 2, 2, 3, 2], 9,
    [1, 1, 3, 3, 4, 4, 6, 2, 2],
    [{-2, 0}, {2}, {1}, {-1}, {-2, -1, 1, 2}, {}, {0}, {0}, {2}],
    [3, 4, 2, 5, 2, 5, 2, 0, 0]);

% A single variable, whose only node goes straight to the terminal.
array[1..1] of var 0..4: b;
constraint mdd(b, 1, [1], 1, [1], [{1, 3}], [0]);

% A variable repeated in x, alongside a constant.
var 1..3: c;
constraint mdd([c, 3, c], 3, [1, 2, 3], 4,
    [1, 2, 2, 3], [{1, 2}, {3}, {1}, {2}], [2, 3, 3, 0]);

solve satisfy;
output ["ENUMSOL: \(a) \(b) \(c)"];
