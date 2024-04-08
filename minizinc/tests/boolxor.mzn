var bool: a;
var bool: b;
var bool: c;

constraint (c = a xor b);
solve satisfy;
output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b) ++ " " ++ show(c)];
