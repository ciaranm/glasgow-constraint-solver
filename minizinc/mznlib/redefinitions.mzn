include "nosets.mzn";

% The standard library's decreasing and strictly_decreasing have overloads for
% var bool, var opt float, var opt $$E and var set of $$E, but none for plain
% var $$E, so an int or enum array takes the optional overload and is
% decomposed (issue #1146). These overloads send it to increasing over the
% reversed array instead, which reaches glasgow_increasing_int or
% glasgow_strictly_increasing_int, and leave the reified forms to the standard
% library. The parameter is called xs because MiniZinc 2.10 warns when
% overloads that differ only in optionality disagree on parameter names, and
% that is its standard library's spelling.
include "increasing.mzn";
include "strictly_increasing.mzn";
predicate decreasing(array [$X] of var $$E: xs) = increasing(reverse(array1d(xs)));
predicate strictly_decreasing(array [$X] of var $$E: xs) = strictly_increasing(reverse(array1d(xs)));
