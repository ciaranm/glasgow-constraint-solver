predicate glasgow_member_int(array[int] of var int: x, var int: y);
predicate fzn_member_int(array[int] of var int: x, var int: y) = glasgow_member_int(x, y);
