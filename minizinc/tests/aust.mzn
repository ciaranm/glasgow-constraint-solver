% https://www.minizinc.org/doc-2.8.3/en/modelling.html

% Colouring Australia using nc colours
int: nc = 3;

var 1..nc: wa;   var 1..nc: nt;  var 1..nc: sa;   var 1..nc: q;
var 1..nc: nsw;  var 1..nc: v;   var 1..nc: t;

constraint wa != nt;
constraint wa != sa;
constraint nt != sa;
constraint nt != q;
constraint sa != q;
constraint sa != nsw;
constraint sa != v;
constraint q != nsw;
constraint nsw != v;

solve satisfy;

output ["ENUMSOL: wa=\(wa) nt=\(nt) sa=\(sa) q=\(q) nsw=\(nsw) v=\(v) t=\(t)"];
