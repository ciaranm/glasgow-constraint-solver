predicate glasgow_lex_less_bool_reif(array[int] of var bool: x, array[int] of var bool: y, var bool: c);
predicate fzn_lex_less_bool_reif(array[int] of var bool: x, array[int] of var bool: y, var bool: c) = glasgow_lex_less_bool_reif(x, y, c);
