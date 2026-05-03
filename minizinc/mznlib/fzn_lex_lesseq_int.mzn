predicate glasgow_lex_lesseq_int(array[int] of var int: x, array[int] of var int: y);
predicate fzn_lex_lesseq_int(array[int] of var int: x, array[int] of var int: y) = glasgow_lex_lesseq_int(x, y);
