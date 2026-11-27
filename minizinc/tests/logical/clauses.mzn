% The clause-like Boolean builtins with literals mixed in, variables repeated,
% and empty arrays (#1006). These are written as direct calls to the FlatZinc
% builtins, which MiniZinc passes through untouched, so each reaches its branch
% in fzn-glasgow exactly as written.
var bool: p; var bool: q; var bool: s; var bool: t;

% p appears positively and negatively, so this always holds.
constraint bool_clause([p, q], [p]);
% Constants on both sides: q \/ not s.
constraint bool_clause([q, false], [true, s]);
% No positive literals: not s \/ not t.
constraint bool_clause([], [s, t]);
% p twice cancels: q xor t.
constraint array_bool_xor([p, p, q, t]);

var bool: r1; var bool: r2; var bool: r3; var bool: r4;
var bool: r5; var bool: r6; var bool: r7;
% Always true, always false, and p \/ not s.
constraint bool_clause_reif([p], [p], r1);
constraint bool_clause_reif([], [], r2);
constraint bool_clause_reif([false, p], [s, true], r7);
% The empty conjunction is true; p /\ true /\ p is p.
constraint array_bool_and([], r3);
constraint array_bool_and([p, true, p], r4);
% q /\ q is q; p xor p is false.
constraint bool_and(q, q, r5);
constraint bool_xor(p, p, r6);

solve satisfy;
output ["ENUMSOL: \([p, q, s, t]) \([r1, r2, r3, r4, r5, r6, r7])"];
