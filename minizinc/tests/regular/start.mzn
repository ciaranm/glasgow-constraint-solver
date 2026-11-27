include "regular.mzn";

% Automata whose start state is not state 1 (#1328). fzn-glasgow renumbers the
% states so that the start state becomes Regular's state 0; it used to rename
% only the transition targets, not the rows of the table or the final states,
% so each of these was solved over a different automaton.

% The start state is the second of three. From 2, 1 -> 3 and 2 -> 1; state 1
% reads anything back to itself; from 3, 2 -> 2 and 1 has no transition. F = {1}.
array[1..3] of var 1..2: a;
array[1..3, 1..2] of int: da = [| 1, 1 | 3, 1 | 0, 2 |];
constraint regular(a, 3, 2, da, 2, {1});

% The start state is the last of three.
array[1..4] of var 1..2: b;
array[1..3, 1..2] of int: db = [| 2, 1 | 2, 3 | 1, 2 |];
constraint regular(b, 3, 2, db, 3, {2});

% The start state is the only final state, so the final states must be
% renumbered along with it.
array[1..3] of var 1..2: c;
array[1..2, 1..2] of int: dc = [| 1, 2 | 1, 2 |];
constraint regular(c, 2, 2, dc, 2, {2});

% The enum form, whose states the standard library numbers in enum order, so
% a start state other than the first member arrives as q0 > 1.
enum S = {P, Q, R};
array[1..3] of var 1..2: e;
array[S, 1..2] of opt S: de = [| P, Q | <>, R | P, R |];
constraint regular(e, de, Q, {R});

solve satisfy;
output ["ENUMSOL: " ++ join(" ", [show(v) | v in a ++ b ++ c ++ e])];
