% A size that can be negative is refused with an error, where the standard
% library's pairwise decomposition would admit it: see the MiniZinc footnote
% in dev_docs/constraints/disjunctive_2d.md (#1251).
predicate fzn_diffn_nonstrict(array[int] of var int: x, array[int] of var int: y,
    array[int] of var int: dx, array[int] of var int: dy) =
    glasgow_diffn_nonstrict(x, y, dx, dy);
