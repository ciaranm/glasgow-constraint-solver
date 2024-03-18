var 2..5: a;
var 3..6: b;
var 1..5: c;
var 1..6: d;

constraint (c = max(a, b));
constraint (d = min(a, b));
solve maximize (c - d);
