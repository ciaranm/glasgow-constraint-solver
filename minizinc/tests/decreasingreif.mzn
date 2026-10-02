include "globals.mzn";

% Reified decreasing and strictly_decreasing have no builtin, so they are left to
% the standard library's decompositions. redefinitions.mzn's overloads for the
% plain forms must not stop these from flattening (#1146).
array[1..3] of var 1..3: x;
var bool: r;
constraint r <-> decreasing(x);

array[1..2] of var 1..3: y;
var bool: q;
constraint q -> strictly_decreasing(y);

solve satisfy;

output ["ENUMSOL: \(x) \(r) \(y) \(q)"];
