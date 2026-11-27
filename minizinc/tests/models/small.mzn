var 1..5: a;
var 1..6: b;
constraint (a + b == 4);
solve satisfy;
output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b)];
