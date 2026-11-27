% A variable that is its own negation: unsatisfiable (#1006).
var bool: p;
constraint bool_not(p, p);

solve satisfy;
output ["ENUMSOL: \(p)"];
