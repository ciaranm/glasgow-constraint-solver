include "globals.mzn";

array[1..5] of var 1..5: xs;
constraint (xs[1] <= 3);
constraint (xs[2] <= 2);
constraint (xs[3] + xs[4] = xs[5]);
constraint (alldifferent(xs));

solve satisfy;
