include "globals.mzn";

% Two arrays indexed from far apart and far from 1, each one's values the
% other's indices: the starts reach Inverse as constants taken from the
% model, and either one read as 1, or as the other's start, leaves no solution
% or the wrong ones. Variety beside offset.mzn, which catches the same
% mutations.
array[1000000..1000002] of var 5000..5002: f;
array[5000..5002] of var 1000000..1000002: g;

constraint inverse(f, g);
constraint f[1000000] != 5000;

solve satisfy;

output ["ENUMSOL: \(f) \(g)"];
