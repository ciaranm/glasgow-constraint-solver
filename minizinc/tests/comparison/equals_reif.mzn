var 1..3: a;
var 1..3: b;
var bool: c;
constraint (a == b) <-> c;

solve satisfy;
output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b) ++ " " ++ show(c)];
