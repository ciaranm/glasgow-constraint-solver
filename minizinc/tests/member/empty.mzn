include "globals.mzn";

% Nothing is a member of an empty array, and the call reaches
% glasgow_member_int as it is: unsatisfiable, and the proof has to say so.
array[1..0] of var 1..3: e;
var 1..3: y;

constraint member(e, y);

solve satisfy;

output ["ENUMSOL: \(y)"];
