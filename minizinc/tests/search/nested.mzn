% The structure of search annotations rather than their heuristics (issue
% #1006): seq_search nested three deep, a seq_search of one, bool_search, an
% int_search over an array mixing integer literals with variables and indexed
% from 0, one over an empty array, one over an array the flattener has fixed
% entirely, one over a variable the model defines (s), and three annotations on
% one solve item, which fzn_glasgow.cc composes in its own order. None of it
% may change the solutions.
include "globals.mzn";

array[0..3] of var -1..2: x;
array[1..3] of var bool: bs;
array[1..2] of var 0..5: fixed;
var -3..3: y;
var int: s = sum(x);

constraint all_different(x);
constraint bs[1] \/ bs[2];
constraint y != 0 /\ (y > 0 <-> bs[3]);
constraint s + y >= 2;
constraint fixed = [4, 1];

solve
  :: seq_search([
      int_search([x[0], 3, x[1]], first_fail, indomain_median),
      seq_search([
        bool_search(bs, input_order, indomain_max),
        seq_search([int_search([y], dom_w_deg, indomain_split)])]),
      int_search([], input_order, indomain_min),
      int_search(fixed, input_order, indomain_min),
      int_search([s], input_order, indomain_max)])
  :: bool_search([bs[2], true], input_order, indomain_min)
  :: int_search(x, smallest, outdomain_max)
  satisfy;

output ["ENUMSOL: \(x) \(bs) \(y) \(fixed)"];
