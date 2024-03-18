include "globals.mzn";

array[1..5] of var 1..10: as;
var int: x;
var int: y;
constraint x = min(as);
constraint y = max(as);
constraint alldifferent(as);
constraint sum(as) = 20;
solve maximize x + y;

