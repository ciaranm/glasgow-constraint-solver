include "globals.mzn";

% As empty.mzn, for dreachable, which has its own redefinition file and so its
% own chance of a wrong guard.
array[1..0] of int: f = [];
array[1..0] of int: t = [];
array[1..0] of var bool: ns;
array[1..0] of var bool: es;
var 1..3: r;

constraint dreachable(f, t, r, ns, es);

solve satisfy;

output ["ENUMSOL: \(r)"];
