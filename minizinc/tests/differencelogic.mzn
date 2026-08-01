% Exercises the difference-logic presolver (--difference-logic), which needs no
% predicate of its own: MiniZinc flattens `t[i] + 2 <= t[i+1]` straight to
% int_lin_le([1,-1], [t_i, t_i+1], -2), and a two-term int_lin_le with
% coefficients +1 and -1 is exactly the shape gcs::DifferenceLogic lifts.
%
% A time-lag network: four events, each at least 2 apart in order, spanning at
% most 8 from first to last. Every one of those four constraints is an edge.
% The last two constraints are deliberately *not* difference-shaped, so the
% presolver's skip counters have something in them too and the test pins the
% classification rather than just the total.

int: n = 4;
array[1..n] of var 0..9: t;

% four difference edges: the chain, and the span closing it
constraint forall (i in 1..n - 1) (t[i] + 2 <= t[i + 1]);
constraint t[n] - t[1] <= 8;

% not two terms, and not unit coefficients: skipped, and counted as such
constraint t[1] + t[2] + t[3] <= 14;
constraint 2 * t[1] - t[3] <= 7;

solve satisfy;

output ["ENUMSOL: t=\(t)\n"];
