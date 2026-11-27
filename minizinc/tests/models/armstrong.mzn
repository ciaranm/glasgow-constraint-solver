% Three-digit Armstrong numbers, those equal to the sum of the cubes of their
% digits: 153, 370, 371 and 407. Variety (issue #1006): the digits come from
% int_div and int_mod, and each cube from pow with a constant exponent, which
% the standard library turns into a chain of int_times.
var 100..999: n;
var 1..9: a;
var 0..9: b;
var 0..9: c;

constraint a = n div 100;
constraint b = (n div 10) mod 10;
constraint c = n mod 10;
constraint n = pow(a, 3) + pow(b, 3) + pow(c, 3);

solve satisfy;

output ["ENUMSOL: \(n)"];
