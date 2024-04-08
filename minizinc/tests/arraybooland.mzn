array[1..5] of var bool: as;
var bool: b;

constraint (b <-> as[1] /\ as[2] /\ as[3] /\ as[4] /\ as[5]);
solve satisfy;

output ["ENUMSOL: " ++ show(as) ++ " " ++ show(b)];

