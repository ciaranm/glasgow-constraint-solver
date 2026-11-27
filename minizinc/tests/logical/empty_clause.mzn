% The empty clause, which nothing satisfies (#1006).
constraint bool_clause([], []);

solve satisfy;
output ["ENUMSOL: x"];
