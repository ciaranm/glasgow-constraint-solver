array[1..5] of var bool: as;

constraint (array_bool_xor(as));
solve satisfy;

output ["ENUMSOL: " ++ show(as)];


