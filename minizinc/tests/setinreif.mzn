var 1..20: x;
var bool: c;

constraint (c <-> x in {5, 6, 7, 10, 11, 12, 13});
solve satisfy;

output ["ENUMSOL: " ++ show(x) ++ " " ++ show(c)];
