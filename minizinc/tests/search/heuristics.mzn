% Every variable and value heuristic fzn_glasgow.cc names, and some it does not
% (issue #1006), each in its own int_search over two variables of a seq_search.
% The supported ones are input_order, first_fail, dom_w_deg and smallest, and
% indomain, indomain_min, indomain_max, indomain_median, outdomain_max,
% outdomain_min, indomain_split, indomain_split_random and indomain_random; the
% rest (anti_first_fail, largest, occurrence, most_constrained, max_regret,
% indomain_reverse_split, indomain_interval and indomain_middle) fall back with
% a warning. The search is complete whatever it picks, so the solutions must be
% the same in every case; what the lane checks is that each value order
% branches over a domain with holes and negative values without losing or
% repeating a value. The sum leaves every variable in {-2, 0, 2} until its
% group is reached, and there are 24 + 276 solutions: one -2, or two 0s.
array[1..24] of var {-2, 0, 2}: g;

constraint sum(g) = 44;

solve :: seq_search([
    int_search([g[1], g[2]], input_order, indomain),
    int_search([g[3], g[4]], first_fail, indomain_min),
    int_search([g[5], g[6]], dom_w_deg, indomain_max),
    int_search([g[7], g[8]], smallest, indomain_median),
    int_search([g[9], g[10]], anti_first_fail, outdomain_max),
    int_search([g[11], g[12]], largest, outdomain_min),
    int_search([g[13], g[14]], occurrence, indomain_split),
    int_search([g[15], g[16]], most_constrained, indomain_split_random),
    int_search([g[17], g[18]], max_regret, indomain_random),
    int_search([g[19], g[20]], input_order, indomain_reverse_split),
    int_search([g[21], g[22]], first_fail, indomain_interval),
    int_search([g[23], g[24]], smallest, indomain_middle)
  ]) satisfy;

output ["ENUMSOL: \(g)"];
