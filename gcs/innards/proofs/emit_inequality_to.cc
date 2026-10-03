#include <gcs/innards/integer_overflow.hh>
#include <gcs/innards/proofs/emit_inequality_to.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/simplify_literal.hh>

#include <util/overloaded.hh>

#include <limits>
#include <ostream>

using std::ostream;
using std::string;

using namespace gcs;
using namespace gcs::innards;

namespace
{
    // The magnitudes of the coefficients a row is written with, kept beside the
    // string so that the row's slack is known when its degree is written. The
    // sums saturate rather than overflowing: all they are ever compared with is
    // 2^63.
    struct RowTally
    {
        unsigned long long total = 0;    // sum of |coefficient|
        unsigned long long negative = 0; // sum of |coefficient| over the negative ones

        static auto saturating_add(unsigned long long & to, unsigned long long v) -> void
        {
            to = (to > std::numeric_limits<unsigned long long>::max() - v) ? std::numeric_limits<unsigned long long>::max() : to + v;
        }

        auto add(Integer w) -> void
        {
            // |w| without negating the most negative long long.
            auto magnitude =
                w.raw_value < 0 ? static_cast<unsigned long long>(-(w.raw_value + 1)) + 1ULL : static_cast<unsigned long long>(w.raw_value);
            saturating_add(total, magnitude);
            if (w.raw_value < 0)
                saturating_add(negative, magnitude);
        }
    };

    // VeriPB normalises a row to non-negative coefficients, which adds the
    // negative coefficients' magnitudes to its degree, and works on a row whose
    // coefficients sum to less than 2^63 in 64-bit arithmetic. Its slack, the
    // sum of the coefficients less the normalised degree, can then overflow:
    // VeriPB 3.0.2 reports a solution as conflicting with such a row when it
    // is not. A row is only in that band if its normalised degree is negative,
    // which makes it trivially true, and half-reifying on a literal that is
    // false (a constant compared with itself, say) writes exactly that, with
    // the whole reification constant in the degree. So give such a row a
    // normalised degree of zero instead: it is still trivially true, so it says
    // the same thing as an OPB row, still follows as a proof line, and only
    // strengthens anything derived from it.
    auto degree_out_of_danger(Integer rhs, const RowTally & tally) -> Integer
    {
        constexpr auto two_to_the_63 = 1ULL << 63;
        if (rhs.raw_value >= 0)
            return rhs;
        auto minus_rhs = static_cast<unsigned long long>(-(rhs.raw_value + 1)) + 1ULL;
        if (tally.negative >= minus_rhs)
            return rhs; // normalised degree is not negative
        auto minus_normalised_degree = minus_rhs - tally.negative;
        if (tally.total < two_to_the_63 && minus_normalised_degree < two_to_the_63 - tally.total)
            return rhs; // slack below 2^63
        // tally.negative < minus_rhs <= 2^63, so this is representable.
        return Integer{-static_cast<long long>(tally.negative)};
    }

    auto append_term_to(string & out, RowTally & tally, Integer w, const string & name) -> void
    {
        tally.add(w);
        append_number_to(out, w);
        out += ' ';
        out += name;
        out += ' ';
    }

    // Render one weighted term of a PB inequality being emitted in >= form:
    // append its literal rendering(s) to `out` with negated weight, or fold a
    // constant term into `rhs`. Shared by the plain and reified renderers so
    // there is exactly one spelling of every term.
    auto append_or_fold_term_to(NamesAndIDsTracker & names_and_ids_tracker, Integer w, const PseudoBooleanTerm & v, string & out, RowTally & tally,
        Integer & rhs, EnsureNames ensure_names) -> void
    {
        overloaded{
            [&](const ProofLiteral & lit) {
                overloaded{
                    [&](const TrueLiteral &) { rhs += w; }, //
                    [&](const FalseLiteral &) {},           //
                    [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                        append_term_to(out, tally, -w,
                            EnsureNames::Yes == ensure_names ? names_and_ids_tracker.pb_file_string_for_ensuring(cond)
                                                             : names_and_ids_tracker.pb_file_string_for(cond));
                    } //
                }
                    .visit(simplify_literal(names_and_ids_tracker, lit));
            },                                                                                                               //
            [&](const ProofFlag & flag) { append_term_to(out, tally, -w, names_and_ids_tracker.pb_file_string_for(flag)); }, //
            [&](const IntegerVariableID & var) {
                overloaded{
                    [&](const SimpleIntegerVariableID & var) {
                        for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(var))
                            append_term_to(out, tally, -w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
                    },
                    [&](const ViewOfIntegerVariableID & view) {
                        // Emit V's own bits when the view is registered (the
                        // typical case — views in constraint bodies are
                        // registered during model writing via
                        // need_all_proof_names_in). Falls back to deviewing
                        // through the underlying for views first seen during
                        // proof logging, which the registry doesn't support.
                        if (auto v_id = names_and_ids_tracker.find_view(view)) {
                            for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(*v_id))
                                append_term_to(out, tally, -w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
                        }
                        else if (! view.negate_first) {
                            for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(view.actual_variable))
                                append_term_to(out, tally, -w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
                            rhs += w * view.then_add;
                        }
                        else {
                            for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(view.actual_variable))
                                append_term_to(out, tally, w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
                            rhs += w * view.then_add;
                        }
                    },
                    [&](const ConstantIntegerVariableID & cvar) { rhs += w * cvar.const_value; } //
                }
                    .visit(var);
            }, //
            [&](const ProofOnlySimpleIntegerVariableID & var) {
                for (const auto & [bit_value, bit_lit] : names_and_ids_tracker.each_bit(var))
                    append_term_to(out, tally, -w * bit_value, names_and_ids_tracker.pb_file_string_for(bit_lit));
            }, //
            [&](const ProofBitVariable & bit) {
                auto [_, bit_name] = names_and_ids_tracker.get_bit(bit);
                append_term_to(out, tally, -w, names_and_ids_tracker.pb_file_string_for(bit_name));
            }, //
        }
            .visit(v);
    }
}

namespace
{
    // Writing a row folds constant terms into the right-hand side and negates
    // every weight to convert <= into >=, so a row whose coefficients and bounds
    // together do not fit in an Integer fails here -- part-way through building
    // the string, with the OPB already half written and nothing in the arithmetic
    // failure naming what was being emitted. Restate it as something a caller can
    // act on. Declared domains are capped (Integer::max_bounded_value()), but
    // auxiliary variables reach further (Integer::max_auxiliary_value()), and
    // large coefficients, or views that offset a domain outwards, can reach
    // this too. See issue #852.
    [[noreturn]] auto rethrow_as_integer_overflow() -> void
    {
        throw IntegerOverflow{"cannot write a pseudo-Boolean row whose coefficients and variable bounds together do not fit in an Integer; "
                              "the variables involved may have domains near Integer::max_bounded_value(), or the coefficients may be too large"};
    }
}

auto gcs::innards::emit_inequality_to(NamesAndIDsTracker & names_and_ids_tracker, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
    string & out, EnsureNames ensure_names) -> void
{
    // build up the inequality, adjusting as we go for constant terms,
    // and converting from <= to >=.
    try {
        Integer rhs = -ineq.rhs;
        RowTally tally;
        for (auto & [w, v] : ineq.lhs.terms) {
            if (0_i == w)
                continue;
            append_or_fold_term_to(names_and_ids_tracker, w, v, out, tally, rhs, ensure_names);
        }

        out += ">= ";
        append_number_to(out, degree_out_of_danger(rhs, tally));
    }
    catch (const IntegerOverflow &) {
        rethrow_as_integer_overflow();
    }
}

auto gcs::innards::emit_reified_inequality_to(NamesAndIDsTracker & names_and_ids_tracker, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq,
    const HalfReifyOnConjunctionOf & half_reif, string & out, EnsureNames ensure_names) -> void
{
    // Renders exactly what emit_inequality_to would produce for
    // reify(ineq, half_reif), without materialising the reified sum: the
    // base terms, then each negated reifying term with the reification
    // coefficient, converted from <= to >= as usual.
    auto shape = names_and_ids_tracker.reification_shape(ineq, half_reif);

    try {
        Integer rhs = -shape.effective_rhs;
        RowTally tally;
        for (auto & [w, v] : ineq.lhs.terms) {
            if (0_i == w)
                continue;
            append_or_fold_term_to(names_and_ids_tracker, w, v, out, tally, rhs, ensure_names);
        }

        // Each reifying term appears negated. A flag or bit negation is a cheap
        // struct copy, but negating a condition literal builds a whole new
        // variant chain just to name it -- and both polarities of a condition are
        // always introduced together, so the negated condition's literal IS the
        // negation of the condition's literal. Look up the condition as given and
        // flip the XLiteral instead.
        auto w = shape.reif_coefficient;
        for (auto & r : half_reif)
            overloaded{
                [&](const ProofFlag & f) { append_or_fold_term_to(names_and_ids_tracker, w, ! f, out, tally, rhs, ensure_names); }, //
                [&](const ProofLiteral & lit) {
                    overloaded{
                        [&](const TrueLiteral &) { /* negated: contributes nothing */ }, //
                        [&](const FalseLiteral &) { rhs += w; },                         //
                        [&]<typename T_>(const VariableConditionFrom<T_> & cond) {
                            auto xlit = EnsureNames::Yes == ensure_names ? names_and_ids_tracker.xliteral_for_ensuring(cond)
                                                                         : names_and_ids_tracker.xliteral_for(cond);
                            append_term_to(out, tally, -w, names_and_ids_tracker.pb_file_string_for(! xlit));
                        } //
                    }
                        .visit(simplify_literal(names_and_ids_tracker, lit));
                },                                                                                                                            //
                [&](const ProofBitVariable & bit) { append_or_fold_term_to(names_and_ids_tracker, w, ! bit, out, tally, rhs, ensure_names); } //
            }
                .visit(r);

        out += ">= ";
        append_number_to(out, degree_out_of_danger(rhs, tally));
    }
    catch (const IntegerOverflow &) {
        rethrow_as_integer_overflow();
    }
}

auto gcs::innards::emit_inequality_to(
    NamesAndIDsTracker & names_and_ids_tracker, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, ostream & stream) -> void
{
    string out;
    emit_inequality_to(names_and_ids_tracker, ineq, out, EnsureNames::No);
    stream << out;
}
