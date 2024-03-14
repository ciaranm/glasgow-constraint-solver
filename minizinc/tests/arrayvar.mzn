array[1..3] of var 1..3: xs;
constraint (xs[xs[1]] = xs[xs[2]] + xs[xs[3]]);
solve satisfy;
