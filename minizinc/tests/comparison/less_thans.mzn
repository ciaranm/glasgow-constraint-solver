var 1..5: a;
var 1..5: b;
var 1..5: c;
var bool: d;
var bool: e;

constraint (int_lt(a, b));
constraint (int_le(b, c));
constraint (int_lt_reif(a, c, d));
constraint (int_le_reif(b, c, e));

solve satisfy;
output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b) ++ " " ++ show(c) ++ " " ++ show(d) ++ " " ++ show(e)];
