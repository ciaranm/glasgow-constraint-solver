predicate glasgow_diffn(array[int] of var int: x, array[int] of var int: y,
    array[int] of var int: dx, array[int] of var int: dy);

predicate glasgow_diffn_nonstrict(array[int] of var int: x, array[int] of var int: y,
    array[int] of var int: dx, array[int] of var int: dy);

% A size that can be negative is refused with an error, where the standard
% library's pairwise decomposition would admit it: see the noOverlap footnote
% in dev_docs/frontend-support-matrix.md (#1251).
predicate fzn_diffn(array[int] of var int: x, array[int] of var int: y,
    array[int] of var int: dx, array[int] of var int: dy) =
    glasgow_diffn(x, y, dx, dy);
