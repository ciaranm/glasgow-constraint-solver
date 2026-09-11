#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_GF2_SYSTEM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_GF2_SYSTEM_HH 1

#include <gcs/constraint_id.hh>
#include <gcs/constraints/parity/parity_chain.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/propagators-fwd.hh>
#include <gcs/variable_condition.hh>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief A set of GF(2) row indices, or of atom indices: a fixed-width bit
     * vector with XOR, which is the only operation either use needs.
     *
     * Rows are XORed together during elimination and so are the origin sets
     * that record which posted rows a working row is the sum of, and those are
     * the same operation over different index spaces.
     *
     * \ingroup Innards
     */
    class GF2Bits
    {
    private:
        std::vector<std::uint64_t> _words;

    public:
        explicit GF2Bits(std::size_t size = 0) : _words((size + 63) / 64, 0)
        {
        }

        auto set(std::size_t i) -> void
        {
            _words[i / 64] |= std::uint64_t{1} << (i % 64);
        }

        auto flip(std::size_t i) -> void
        {
            _words[i / 64] ^= std::uint64_t{1} << (i % 64);
        }

        auto reset(std::size_t i) -> void
        {
            _words[i / 64] &= ~(std::uint64_t{1} << (i % 64));
        }

        [[nodiscard]] auto test(std::size_t i) const -> bool
        {
            return 0 != (_words[i / 64] & (std::uint64_t{1} << (i % 64)));
        }

        auto operator^=(const GF2Bits & other) -> GF2Bits &
        {
            for (std::size_t w = 0; w != _words.size(); ++w)
                _words[w] ^= other._words[w];
            return *this;
        }

        [[nodiscard]] auto none() const -> bool;

        /// How many bits are set. Only ever compared against 0, 1 and 2, but
        /// counting is no more expensive than stopping early over words.
        [[nodiscard]] auto count() const -> std::size_t;

        /// The index of the lowest set bit, or nullopt if there is none.
        [[nodiscard]] auto first_set() const -> std::optional<std::size_t>;

        /// Every index that is set, lowest first.
        [[nodiscard]] auto set_indices() const -> std::vector<std::size_t>;
    };

    /**
     * \brief One row of a GF(2) system: the XOR of the atoms whose bits are
     * set equals \c rhs.
     *
     * \ingroup Innards
     */
    struct GF2Row
    {
        GF2Bits atoms;

        /// Which posted rows this is the XOR of. For a posted row, just itself;
        /// for a row elimination produced, everything that went into it. This
        /// is what a justification cites, so it is maintained even when proofs
        /// are off --- the cost is one word of XOR per elimination step.
        GF2Bits origin;

        bool rhs = false;
    };

    /**
     * \brief A system of odd-parity rows over literals, canonicalised so that
     * every column is a distinct positive atom.
     *
     * gcs literals come in negated pairs (`v != c` is `!(v == c)`, `v < c` is
     * `!(v >= c)`), and GF(2) has no notion of a negated variable: `!p` is
     * `p XOR 1`, so a negation is a column entry plus a flip of the row's
     * right-hand side. Canonicalising to the positive form of each pair is
     * what makes two rows that mention the same underlying fact share a column,
     * and so is what makes them cancel --- both here and, later, in the `pol`
     * that adds their pseudo-Boolean rows.
     *
     * Two atoms that are semantically equivalent without being a negation pair
     * (`v != 0` and `v == 3` where the domain is `{0, 3}`) stay separate
     * columns. That loses strength and never soundness: the system is a
     * relaxation in which every atom is free, which is exactly what the
     * pseudo-Boolean rows state, so the propagator and the proof agree about
     * what is being claimed.
     *
     * \ingroup Innards
     */
    struct GF2System
    {
        std::vector<IntegerVariableCondition> atoms;
        std::vector<GF2Row> rows;
    };

    /**
     * \brief Turn posted rows of literals, each asserting odd parity, into a
     * canonicalised GF2System.
     *
     * Duplicate atoms within a row cancel, and `TrueLiteral` / `FalseLiteral`
     * fold into the right-hand side. Rows are kept even when they come out
     * empty: an empty row with an odd right-hand side is a contradiction the
     * propagator still has to report.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto build_gf2_system(const std::vector<Literals> & posted_rows) -> GF2System;

    /**
     * \brief Split the positive atom out of a literal, and say whether the
     * literal was its negation.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto canonical_atom(const IntegerVariableCondition & lit) -> std::pair<IntegerVariableCondition, bool>;

    /**
     * \brief Reduce every row to reduced row echelon form in place, and report
     * how many rows are non-zero.
     *
     * The rows left below the rank are all-zero in their atoms; those with an
     * odd right-hand side are the contradictions.
     *
     * \ingroup Innards
     */
    auto gauss_jordan(std::vector<GF2Row> & rows, std::size_t n_atoms) -> std::size_t;

    /**
     * \brief One row a ParitySystem propagator is to reason over, with
     * everything its proofs will need to cite about that row.
     *
     * The three fields travel together because they have to: the chain is the
     * chain *of these literals*, and getting them out of step would produce a
     * justification citing rows about something else. Passing them as three
     * parallel vectors is what this exists instead of.
     *
     * \ingroup Innards
     */
    struct ParitySystemRow
    {
        /// An odd number of these is true.
        Literals literals;

        /// How this row's slack form is to be derived: the accumulator chain in
        /// the `.opb` for exactly these literals, or the claim that two RUP lines
        /// will do. Nullopt when proofs are off, which is also when nothing reads
        /// it.
        std::optional<ParitySlackSource> slack_source;

        /// Names the fresh per-step variables the slack-form derivation
        /// introduces. Only ever cosmetic --- a flag's identity is its index,
        /// not its name --- but a readable `.pbp` is worth the parameter.
        std::string flag_stem;
    };

    /**
     * \brief Install a propagator doing Gauss-Jordan over a system of
     * odd-parity rows, and the initialiser that derives the proofs it needs.
     *
     * Two things are installed rather than one. The slack-form rows the
     * justifications cite have to be derived inside the proof, at
     * ProofLevel::Top, and an initialiser is where that can happen: it runs once
     * before search, with a logger, which is later than a ProofModel is
     * available and earlier than any inference needs the rows. See
     * dev_docs/parity-system.md.
     *
     * Called from ParitySystem, which emitted its own chains, and from
     * ParitySystemGathering, which found other constraints'. Neither owns the
     * algorithm, which is why it lives here.
     *
     * A row over no literals says that zero is odd. It cannot be eliminated over
     * and has no slack row, so rather than leave a caller to remember that, this
     * installs an initial contradiction for the whole constraint instead of a
     * propagator --- which is what such a row means anyway. `constraint_type`
     * names the component in the note that gets reported when it does. A caller
     * that would rather leave an empty row to whoever else is enforcing it
     * should not pass it in.
     *
     * \ingroup Innards
     */
    auto install_parity_system_propagator(
        Propagators & propagators, const ConstraintID & id, const std::string & constraint_type, std::vector<ParitySystemRow> rows) -> void;
}

#endif
