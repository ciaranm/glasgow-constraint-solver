var set of 0..9: s;
constraint sum (i in s) (1) = 3;
constraint sum (i in s) (i) = 9;
solve satisfy;
output ["ENUMSOL: " ++ show(s)];

