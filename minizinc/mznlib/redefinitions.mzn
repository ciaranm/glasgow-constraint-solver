
predicate glasgow_ne(var int: a, var int: b);

predicate int_lin_ne(array[int] of int: as, array[int] of var int: bs, int: c) =
    if ((as == [-1, 1] \/ as == [1, -1]) /\ c == 0) then
        glasgow_ne(bs[1], bs[2])
    else
        abort("int_lin_ne not fully supported")
    endif
