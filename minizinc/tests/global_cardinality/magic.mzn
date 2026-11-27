include "globals.mzn";

% The magic sequence: s[i] is the number of times i occurs in s, so every count
% is one of the variables being counted. The Hall reasoning's justifications read
% the counts' bounds, and they used to be run after the inference they justified
% had been pushed, so when that inference moved a count, the proof cited the new
% bound while the reason stated the old one and VeriPB rejected it (#1191). n = 6
% has no solution, and was one of the rejected sizes.
int: n = 6;
array[0..n-1] of var 0..n-1: s;

constraint global_cardinality(s, array1d(0..n-1, [i | i in 0..n-1]), s);

solve satisfy;
output ["ENUMSOL: " ++ show(s)];
