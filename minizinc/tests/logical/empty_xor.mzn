% An odd number of an empty array's members are true: unsatisfiable (#1006).
constraint array_bool_xor([]);

solve satisfy;
output ["ENUMSOL: x"];
