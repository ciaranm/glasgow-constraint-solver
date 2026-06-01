predicate glasgow_arg_sort_int(array[int] of var int: x, array[int] of var int: p);

% At the FlatZinc level arg_sort is 1-based: p is iterated over 1..length(x) and
% its values index into x's (1-based) index set. The C++ ArgSort takes that
% index base as an offset (here 1), so no shifting is needed in the redirection.
predicate fzn_arg_sort_int(array[int] of var int: x, array[int] of var int: p) =
    glasgow_arg_sort_int(x, p);
