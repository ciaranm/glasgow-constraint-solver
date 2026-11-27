var 3..5: a;
var -2..6: b;
var -10..20: c;
constraint (c = a * b);
solve satisfy;
output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b) ++ " " ++ show(c)];
