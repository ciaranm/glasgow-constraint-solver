% MiniZinc gives us `x - y <= d` as a two-term int_lin_le, which the reader
% recovers as LessThanEqual. All four unit-coefficient sign patterns appear
% below --- an inequality does not survive being divided by a negative, so the
% pairs with a negative *first* coefficient are the ones that have to swap
% operands, and without them a normalisation that never swaps passes this test.
% The patterns are what the flattener produces, not what the source looks like:
% `x - y <= d` gives [1, -1], `x - y >= d` gives [-1, 1], and both `-x - y <= d`
% and `x + y >= d` give [-1, -1].
%
% The difference-logic presolver enumerates ReifiedCompareLessThanOrMaybeEqual
% donors as well as ReifiedLinearInequality ones, and deviews each operand, so
% the recovered form lifts the same edges the two-term linear form did: that is
% what the --difference-logic lane pins. The [1, 1] and [-1, -1] rows are not
% difference-shaped and must not lift either way --- before the rewrite the
% presolver declines them for their coefficients, afterwards for being a negated
% view, which is the same decision.
array[1..6] of var 0..4: t;

constraint t[1] - t[2] <= 3;   % [1, -1]
constraint t[2] - t[3] <= -2;  % [1, -1]
constraint t[3] - t[4] >= -1;  % [-1, 1]
constraint t[4] - t[5] >= -2;  % [-1, 1]
constraint t[5] - t[6] <= 4;   % [1, -1]
constraint t[6] - t[1] <= 7;   % [1, -1]
constraint t[1] + t[2] <= 4;   % [1, 1], not difference-shaped
constraint -t[3] - t[4] <= 3;  % [-1, -1], not difference-shaped

solve satisfy;

output ["ENUMSOL: " ++ show(t)];
