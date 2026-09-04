predicate glasgow_regular(array[int] of var int: x, int: Q, int: S, array[int] of int: d, int: q0, set of int: F);

% FlatZinc regular numbers its alphabet 1..S, and gcs's Regular takes the symbol
% values it is given rather than assuming an alphabet, so x is handed over
% untouched and the transition table is keyed 1..S on the solver side.
%
% This used to shift instead -- `[x[i] - 1 | i in index_set(x)]` -- which is a
% worse idea than it looks. The comprehension introduces a fresh FlatZinc
% variable per position, declared over the full range before its defining
% int_lin_eq has propagated, and gcs's LinearEquality is bounds consistent by
% default, so a hole punched in either copy reaches the other only as a bound.
% Regular prunes by removing individual values, and a search annotation names
% the model's own array, so both the propagation and the brancher's view of the
% domain sizes were being lost in the shift. See fzn_bin_packing_capa.mzn, whose
% sibling problem needs an offset passed because BinPacking does fix its bin
% numbering; here no offset is needed at all.
predicate fzn_regular(array[int] of var int: x, int: Q, int: S, array[int,int] of int: d, int: q0, set of int: F) =
    glasgow_regular(x, Q, S, array1d(d), q0, F);
