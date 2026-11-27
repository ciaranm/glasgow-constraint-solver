var -4..4: a;
var -3..3: b;
constraint (abs(a) == b);
solve satisfy;
output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b)];
