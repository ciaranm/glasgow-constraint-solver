include "globals.mzn";

% As empty.mzn, over bools, which reaches glasgow_member_bool.
array[1..0] of var bool: e;
var bool: y;

constraint member(e, y);

solve satisfy;

output ["ENUMSOL: \(y)"];
