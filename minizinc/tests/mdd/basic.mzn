include "mdd.mzn";

% The XCSP3-core mdd reference example, expressed in MiniZinc's representation:
% nodes 1..6 correspond to r, n1, n2, n3, n4, n5; node 0 is the implicit T.
%   level: r=1, n1=n2=n3=2, n4=n5=3.
%   edges: (r,0,n1)(r,1,n2)(r,2,n3)
%          (n1,2,n4)(n2,2,n4)(n3,0,n5)
%          (n4,0,t)(n5,0,t)
% Three solutions: (0,2,0), (1,2,0), (2,0,0).

array[1..3] of var 0..2: x;

constraint mdd(x,
               6,
               [1, 2, 2, 2, 3, 3],
               8,
               [1, 1, 1, 2, 3, 4, 5, 6],
               [{0}, {1}, {2}, {2}, {2}, {0}, {0}, {0}],
               [2, 3, 4, 5, 5, 6, 0, 0]);

solve satisfy;
output ["ENUMSOL: " ++ join(" ", [show(v) | v in x])];
