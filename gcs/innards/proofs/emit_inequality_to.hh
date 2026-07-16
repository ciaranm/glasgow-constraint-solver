#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_EMIT_INEQUALITY_TO_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOFS_PROOF_EMIT_INEQUALITY_TO_HH

#include <gcs/expression.hh>
#include <gcs/innards/proofs/names_and_ids_tracker-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/proofs/reification.hh>

#include <charconv>
#include <iosfwd>
#include <string>

namespace gcs::innards
{
    /**
     * \brief Append a number to a string being built up as proof text,
     * without the locale machinery or allocation that streams and
     * to_string bring. Proof lines are assembled with this rather than
     * ostream insertion because it is on the hot path of every logged
     * inference.
     *
     * \ingroup Innards
     */
    inline auto append_number_to(std::string & out, long long v) -> void
    {
        char buf[24];
        auto r = std::to_chars(buf, buf + sizeof(buf), v);
        out.append(buf, r.ptr);
    }

    inline auto append_number_to(std::string & out, Integer v) -> void
    {
        append_number_to(out, v.raw_value);
    }

    /**
     * \brief Should rendering an inequality introduce proof names for
     * conditions that do not have one yet?
     *
     * `Yes` fuses what would otherwise be a separate need_all_proof_names_in
     * pass into rendering: an introduction emits its definition lines to the
     * proof stream mid-render, which is safe precisely because the line being
     * rendered is being assembled in a buffer and written afterwards. The
     * model-writing path must use `No` (with an explicit pre-pass), since its
     * introductions append to the same OPB buffer being rendered into.
     *
     * \ingroup Innards
     */
    enum class EnsureNames
    {
        Yes,
        No
    };

    /**
     * \brief Append an inequality, rendered as OPB / proof text, to a string.
     *
     * Only used inside proof innards.
     *
     * \ingroup Innards
     */
    auto emit_inequality_to(
        NamesAndIDsTracker &, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, std::string & out, EnsureNames ensure_names) -> void;

    /**
     * \brief Write an inequality out to an ostream.
     *
     * Only used inside proof innards.
     *
     * \ingroup Innards
     */
    auto emit_inequality_to(NamesAndIDsTracker &, const SumLessThanEqual<Weighted<PseudoBooleanTerm>> & ineq, std::ostream & stream) -> void;
}

#endif
