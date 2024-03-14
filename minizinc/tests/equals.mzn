array[1..3] of var 1..10: a;
array[1..3] of var 3..7: b;
var 1..3: x;
var 1..3: y;
constraint (a[x] == b[y]);
solve maximize x + y;
