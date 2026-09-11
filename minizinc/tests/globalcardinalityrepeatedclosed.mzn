include "globals.mzn";

% As globalcardinalityrepeated, but closed: value 3 is in the variable domains
% and outside the cover, so the closed restriction forbids it. The fold has to
% leave the *set* of cover values alone -- dropping the repeat must not drop the
% value -- which this checks and the open model cannot (#922).
array[1..3] of var 1..3: x;
array[1..3] of var 0..3: c;

constraint global_cardinality_closed(x, [1, 2, 1], c);

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(c)];
