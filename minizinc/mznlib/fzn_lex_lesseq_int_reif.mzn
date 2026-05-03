predicate glasgow_lex_lesseq_int_reif(array[int] of var int: x, array[int] of var int: y, var bool: c);
predicate fzn_lex_lesseq_int_reif(array[int] of var int: x, array[int] of var int: y, var bool: c) = glasgow_lex_lesseq_int_reif(x, y, c);
