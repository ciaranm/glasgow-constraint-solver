var -5..5: a;
var -5..5: b;
var -20..20: c;
constraint (c = a div b);
solve satisfy;
output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b) ++ " " ++ show(c)];
