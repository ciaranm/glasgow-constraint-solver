include "globals.mzn";

% As empty.mzn, for dpath, which has its own redefinition file and so its own
% chance of a wrong guard.
array[1..0] of int: f = [];
array[1..0] of int: t = [];
array[1..0] of var bool: ns;
array[1..0] of var bool: es;
var 1..3: s;

constraint dpath(f, t, s, s, ns, es);

solve satisfy;

output ["ENUMSOL: \(s)"];
