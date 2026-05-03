predicate glasgow_lex_less_bool(array[int] of var bool: x, array[int] of var bool: y);
predicate fzn_lex_less_bool(array[int] of var bool: x, array[int] of var bool: y) = glasgow_lex_less_bool(x, y);
