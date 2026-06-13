include "alldifferent.mzn";

% Two coupled permutation groups, each searched with its own dom_w_deg. This
% exercises a seq_search of two stateful weightings: each carries its own
% conflict-driven weighting, so the engine must let several conflict observers
% coexist (issue #315). The solution set is differentially checked against the
% reference solver.
array[1..4] of var 1..4: x;
array[1..4] of var 1..4: y;

constraint alldifferent(x);
constraint alldifferent(y);
constraint forall(i in 1..4) (x[i] != y[i]);

solve :: seq_search([
    int_search(x, dom_w_deg, indomain_min),
    int_search(y, dom_w_deg, indomain_min)
]) satisfy;

output ["ENUMSOL: x=\(x) y=\(y)\n"];
