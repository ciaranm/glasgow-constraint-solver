include "globals.mzn";

% f's values are indices of g and g's values are indices of f, and neither
% array is indexed from 1, nor from the same place as the other (regression
% test for issue #987: the front end assumed both started at 1, and Inverse's
% own value set assumed the two starts were equal).
array[0..3] of var 5..8: f;
array[5..8] of var 0..3: g;

constraint inverse(f, g);
constraint f[0] != 5;

solve satisfy;

output ["ENUMSOL: " ++ show(f) ++ " " ++ show(g)];
