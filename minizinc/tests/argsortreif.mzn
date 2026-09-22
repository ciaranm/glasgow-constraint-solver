include "globals.mzn";

% arg_sort in a reified and a half-reified context. The stdlib's arg_sort.mzn
% does not include fzn_arg_sort_int_reif.mzn, so a reified call used to flatten
% the redefinition's body in place, found the builtin inside it with no reified
% form, and failed to flatten at all. The redefinition includes the stdlib's
% reified decomposition now; p's domain reaches past x's index set, which is
% where the two sides disagree most.
array[0..1] of var 0..1: x;
array[1..2] of var -1..1: p;
var bool: r;
var bool: s;

constraint r <-> arg_sort(x, p);
constraint s -> arg_sort(x, p);

solve satisfy;

output ["ENUMSOL: \(x) \(p) \(r) \(s)"];
