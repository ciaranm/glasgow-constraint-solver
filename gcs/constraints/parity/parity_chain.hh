#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_PARITY_CHAIN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_PARITY_PARITY_CHAIN_HH 1

#include <gcs/constraint_id.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/constraint_proof_model_data.hh>
#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>

#include <cstddef>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief What one accumulator chain calls the rows and flags it emits.
     *
     * These are cake_pb_cp's own names, which is what makes them a contract
     * rather than an implementation detail: cake re-derives the same ones from
     * the `.scp`, so renaming any of them is a cross-tool break. A constraint
     * that emits a chain publishes this object through its
     * ConstraintProofModelData, and both the emitter (define_parity_chain) and
     * anything looking a chain up afterwards (find_parity_chain) build every
     * name through it --- so there is exactly one place the names exist, and
     * nobody is guessing at another constraint's scheme.
     *
     * Publishing a small naming *object* rather than a handful of loose
     * role-producing functions is deliberate. ConstraintProofModelData is happy
     * with either --- \c Cumulative publishes several loose functions --- but
     * this family's names are all indexed the same way, by the same optional row
     * index, and bundling them means a citer cannot pick up one of them without
     * the rest or accidentally mix an unprefixed role with a prefixed flag.
     *
     * \ingroup Innards
     */
    struct ParityChainNaming
    {
        /**
         * \brief Which chain, when one constraint emits several.
         *
         * Left unset --- ParityOdd's case, and the only one cake ever sees ---
         * the flags are `x[id][k]` and the roles are `0ge`, `0le`, `<k>_0_0`,
         * which is cake's naming exactly. Set, every flag gains a leading index
         * and every role a leading `r<row>_`, which is what keeps several chains
         * under one identity apart; cake has no counterpart for that, and needs
         * none, because a constraint with several chains has no `.scp` spelling
         * to be checked against.
         */
        std::optional<long long> row;

        /// `1 - a_0 >= 0`. Cake's name, which reads the other way round from
        /// what the row says; kept because it is cake's.
        [[nodiscard]] auto role_0ge() const -> std::string;

        /// `a_0 - 1 >= 0`.
        [[nodiscard]] auto role_0le() const -> std::string;

        /// `-a_n >= 0`.
        [[nodiscard]] auto role_acc() const -> std::string;

        /**
         * \brief One of the four clauses of step `k` (one-based, as cake counts
         * them), naming the `(a_{k-1}, l_k)` case it rules out.
         */
        [[nodiscard]] auto role_step(std::size_t k, bool accumulator_in, bool literal) const -> std::string;

        /// The key of `a_k`, for k in 0..n.
        [[nodiscard]] auto accumulator_flag_key(std::size_t k) const -> ProofFlagKey;
    };

    /**
     * \brief The rows and flags one accumulator chain put in the `.opb`, as the
     * slack-form derivation needs to cite them.
     *
     * Handed back by define_parity_chain, and recoverable afterwards by
     * find_parity_chain, so that the derivation is one piece of code whether the
     * chain was emitted by ParitySystem or by a separately posted ParityOdd that
     * a presolver went looking for.
     *
     * \ingroup Innards
     */
    struct ParityChainRows
    {
        /// The four clauses of one step, `a_{k-1} XOR l_k XOR a_k = 0`, named
        /// for the (accumulator-in, literal) case each one rules out.
        struct Step
        {
            ProofLine c00, c11, c10, c01;
        };

        /// `a_0 .. a_n`: n + 1 of them for a chain over n literals.
        std::vector<ProofFlag> accumulators;
        std::vector<Step> steps;

        /// `a_0 <= 1`, `a_0 >= 1`, and `a_n <= 0`.
        ProofLine a0_le_1, a0_ge_1, an_le_0;
    };

    /**
     * \brief Emit cake_pb_cp's accumulator-chain OPB encoding of "an odd number
     * of these literals is true", under the given constraint's identity.
     *
     * Shared by ParityOdd, which has one chain, and ParitySystem, which has one
     * per row: the point is that both entry points put the *same* rows in the
     * `.opb`, so the slack-form derivation that reads them back
     * (dev_docs/parity-system.md) is one piece of code rather than two.
     *
     * \sa ParityChainNaming, which is where `naming` comes from and what every
     * name emitted here is built through.
     *
     * \ingroup Innards
     */
    auto define_parity_chain(ProofModel & model, const ConstraintID & id, const ParityChainNaming & naming, const Literals & lits) -> ParityChainRows;

    /**
     * \brief Recover a chain that was emitted earlier, by asking the tracker for
     * every row and flag `naming` names.
     *
     * The counterpart of define_parity_chain, for a presolver: a constraint that
     * emitted its own chain still has the struct, but one that means to build
     * proofs on *another* constraint's chain has only that constraint's
     * published naming and the number of literals it was posted with.
     *
     * Returns nullopt when any part of the chain is missing --- proofs are off,
     * the constraint was never installed, or it published a naming whose rows
     * were not emitted. All of those mean the same thing to a caller: there is
     * nothing to cite, so do not do the thing that would need citing. It is
     * deliberately all-or-nothing, because a chain missing one of its four
     * per-step clauses cannot be telescoped, and a partial answer would only
     * move the failure to the `pol`.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto find_parity_chain(const ProofLogger & logger, const ConstraintID & id, const ParityChainNaming & naming,
        std::size_t how_many_literals) -> std::optional<ParityChainRows>;

    /**
     * \brief A row of exactly two literals whose slack form is `l1 + l2 = 1`,
     * with both halves plain RUP against rows the donor already emitted.
     *
     * `B` is zero for such a row --- odd parity over two literals means exactly
     * one of them holds --- so there is nothing to introduce and nothing to
     * telescope. What makes the two halves RUP rather than merely true is the
     * donor's own encoding: a Boolean `Equals` or `NotEquals` states its
     * operands' relationship over their bits, and negating either half fixes
     * both bits and walks straight into one of those rows. A donor claiming this
     * shape is claiming that; it is not a property of being short.
     *
     * \ingroup Innards
     */
    struct ParitySlackFormIsRUP
    {
        [[nodiscard]] auto operator<=>(const ParitySlackFormIsRUP &) const = default;
    };

    /**
     * \brief How one row's slack form is to be derived, which depends on what
     * kind of donor the row came from.
     *
     * Two shapes so far, and the variant rather than a callback because both are
     * short, closed, and worth being able to read: a ParityChainRows row is
     * telescoped out of cake's accumulator chain, and a ParitySlackFormIsRUP row
     * is two RUP lines. A third donor family would add an alternative here and a
     * case to derive_parity_slack_rows, and nothing else.
     *
     * \ingroup Innards
     */
    using ParitySlackSource = std::variant<ParityChainRows, ParitySlackFormIsRUP>;

    /**
     * \brief Derive the two pseudo-Boolean inequalities saying a row's literals
     * sum to `1 + 2B`, and return them.
     *
     * Gocht and Nordstrom's (4.4a) and (4.4b) --- the form under which adding
     * two parity constraints together is one `pol` line. Neither shape of donor
     * states it directly, and a presolver could not add it to the `.opb` even if
     * it wanted to, so it is derived inside the proof at ProofLevel::Top. See
     * dev_docs/parity-system.md, "Deriving the slack row", for the argument, and
     * for why an accumulator chain needs a `red` per step where a two-literal
     * row needs only a RUP.
     *
     * `flag_stem` names the fresh per-step variables a chain introduces, and
     * must be unique across chains; a RUP-shaped row introduces none and ignores
     * it. Returns nullopt for a chain over no literals: there is no step to
     * telescope, `a_0` and `a_n` are the same flag, and nothing is needed --- an
     * empty odd row is a contradiction the chain's own three rows state.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto derive_parity_slack_rows(ProofLogger & logger, const ParitySlackSource & source, const Literals & lits,
        const std::string & flag_stem) -> std::optional<std::pair<ProofLine, ProofLine>>;
}

#endif
