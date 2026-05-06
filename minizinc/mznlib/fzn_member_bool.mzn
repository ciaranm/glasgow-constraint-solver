predicate glasgow_member_bool(array[int] of var bool: x, var bool: y);
predicate fzn_member_bool(array[int] of var bool: x, var bool: y) = glasgow_member_bool(x, y);
