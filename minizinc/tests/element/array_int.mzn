array[1..5] of int: as = [2, 4, 6, 8, 10];
array[1..5] of int: bs = [7, 6, 5, 4, 3];

var 1..5: x;
var 1..5: y;
var 5..17: z;

constraint (x + y == 6);
constraint (z == as[x] + bs[y]);
solve satisfy;

output ["ENUMSOL: " ++ show(x) ++ " " ++ show(y) ++ " " ++ show(z)];
