var 1..10: x;
var 1..10: y;
constraint (x != 3);
constraint (x != 4);
constraint (x != 5);
constraint (x != 6);
constraint (y != 2);
constraint (y != 3);
constraint (y != 7);
constraint (y != 8);

solve satisfy;

output ["ENUMSOL: " ++ show(x) ++ " " ++ show(y)];
