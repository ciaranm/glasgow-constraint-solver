#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_TABULATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_TABULATION_HH

#include <gcs/consistency.hh>
#include <gcs/constraint_id.hh>
#include <gcs/constraints/extensional_utils.hh>
#include <gcs/constraints/innards/triggers.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Under consistency::Auto, constraints tabulate when the enumeration
     * tree (the product of the enumerated variables' domain sizes) is no bigger
     * than this. The proof derivation emits a line per tree node, so this
     * bounds both the work and the proof size.
     *
     * The built-in default is a guess, to be benchmarked properly as a
     * follow-up to issue #444; to make that easy (say, from an autotuner), the
     * GCS_TABULATION_THRESHOLD environment variable overrides it, read once on
     * first use.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto default_tabulation_threshold() -> long long;

    /**
     * \brief An enumerated variable that is functionally determined by the
     * others, for build_table_in_proof().
     *
     * Claiming var asserts two things. First, whenever every other enumerated
     * variable is assigned, at most one of var's values can be accepted, and
     * value() returns that sole candidate (or nullopt when there is none, say
     * because an affine form does not divide): it is passed the assignment
     * vector with every position except var's own filled in. Second, unit
     * propagation against the structural OPB encoding must pin var to that
     * value (or reach a contradiction) once the others are assigned; being
     * semantically determined is not enough, since reverse unit propagation
     * cannot do case analysis.
     *
     * A returned candidate is still checked against the current domain and
     * the acceptance test, so a wrong value() cannot inject a bad tuple; and
     * a candidate it wrongly misses fails proof verification at the parent
     * backtrack line, so mistakes are caught rather than silently dropping
     * solutions.
     *
     * \ingroup Innards
     * \sa gcs::innards::build_table_in_proof()
     */
    struct DeterminedVariable
    {
        IntegerVariableID var;
        std::function<auto(const std::vector<Integer> &)->std::optional<Integer>> value;
    };

    /**
     * \brief Enumerate every assignment to vars that accept() approves, building
     * a table that can be handed to propagate_extensional() to achieve GAC.
     *
     * This is how a constraint can offer tabulated GAC without changing its OPB
     * encoding: the structural encoding stays whatever the constraint defines,
     * and the table is derived in-proof. With proof logging active, each
     * accepted tuple's selector literals are introduced via a pair of RED
     * lines, and every fully-explored subtree is closed with a RUP backtrack
     * line. Those backtrack lines are only verifiable if any complete
     * assignment that accept() rejects unit-propagates to a contradiction
     * against the owning constraint's structural OPB encoding; a caller must
     * make sure its encoding is strong enough for this before using tabulation.
     *
     * The derivation emits a line per enumeration tree node, so the branching
     * order matters: variables are enumerated smallest domain first, which
     * minimises the number of internal nodes.
     *
     * Better still is skipping a level outright, which is what determined_vars
     * buys: whichever of them has the largest domain is branched on last, and
     * its entire level of the enumeration tree is replaced by a single call to
     * its DeterminedVariable::value(), with no backtrack line emitted per
     * value. The parent's backtrack line is still RUP because unit propagation
     * pins the variable, and then either the accepted tuple's selector must
     * hold, or the pinned complete assignment refutes just like any other
     * rejected leaf. Only one level can be skipped this way: higher up the
     * tree, the variables below are unassigned, so being determined by all
     * the others says nothing.
     *
     * Returns nullopt if no assignment is accepted; the caller should then
     * infer FalseLiteral, which is RUP against the structural encoding for the
     * same reason as above. The proof derivation is skipped entirely in
     * assertion mode.
     *
     * The selector_name names the introduced selector literals in the proof
     * log, and comment is emitted before the derivation begins. Intended to be
     * called from an InitialiserPriority::Expensive initialiser; see
     * ReifiedLinearEquality's GAC path for the wiring.
     *
     * \ingroup Innards
     * \sa gcs::innards::propagate_extensional()
     */
    auto build_table_in_proof(const std::vector<IntegerVariableID> & vars, const std::vector<DeterminedVariable> & determined_vars,
        const std::function<auto(const std::vector<Integer> &)->bool> & accept, const std::string & selector_name, const std::string & comment,
        State & state, ProofLogger * const logger) -> std::optional<ExtensionalData>;

    /**
     * \brief Collects the distinct variables a tabulation enumerates over,
     * assigning each a position that the acceptance callback indexes with.
     *
     * The arithmetic constraints deview their arguments and may share an
     * underlying variable between slots (aliased operands), so each slot asks
     * for its variable's position and duplicates collapse.
     *
     * \ingroup Innards
     * \sa gcs::innards::install_tabulation()
     */
    class TabulationVariables
    {
    private:
        std::vector<IntegerVariableID> _vars;

    public:
        [[nodiscard]] auto position_of(const IntegerVariableID & v) -> std::size_t
        {
            for (std::size_t i = 0; i < _vars.size(); ++i)
                if (_vars[i] == v)
                    return i;
            _vars.push_back(v);
            return _vars.size() - 1;
        }

        [[nodiscard]] auto vars() const -> const std::vector<IntegerVariableID> &
        {
            return _vars;
        }
    };

    /**
     * \brief Should a constraint tabulate, given its consistency level and the
     * variables it would enumerate over?
     *
     * Always under consistency::Tabulated, never under consistency::BC, and under
     * consistency::Auto exactly when the enumeration tree (the product of the
     * domain sizes) is within default_tabulation_threshold.
     *
     * \ingroup Innards
     * \sa gcs::innards::install_tabulation()
     */
    [[nodiscard]] auto want_tabulation(const std::variant<consistency::Auto, consistency::BC, consistency::Tabulated> & level,
        const std::vector<IntegerVariableID> & enum_vars, const State & initial_state) -> bool;

    /**
     * \brief The standard wiring for tabulated GAC: an expensive initialiser
     * that derives the table in-proof via build_table_in_proof() (inferring
     * FalseLiteral when no assignment is accepted), and an extensional
     * propagator over the result.
     *
     * The determined_vars are the enumerated variables that are functionally
     * determined by the others, in the strong unit-propagation sense that
     * DeterminedVariable documents; pass an empty vector if there are none.
     *
     * The Hint_ type parameter is the owning constraint's assertion hint,
     * constructed from `owner` alone.
     *
     * \ingroup Innards
     * \sa gcs::innards::build_table_in_proof()
     */
    template <typename Hint_>
    auto install_tabulation(Propagators & propagators, const ConstraintID & owner, std::vector<IntegerVariableID> enum_vars,
        std::vector<DeterminedVariable> determined_vars, std::function<auto(const std::vector<Integer> &)->bool> accept, std::string selector_name,
        std::string comment) -> void
    {
        Triggers triggers;
        triggers.on_change = enum_vars;

        auto data = std::make_shared<std::optional<ExtensionalData>>(std::nullopt);
        propagators.install_initialiser(
            [data = data, enum_vars = std::move(enum_vars), determined_vars = std::move(determined_vars), accept = std::move(accept),
                selector_name = std::move(selector_name), comment = std::move(comment),
                owner = owner](State & state, auto & inference, ProofLogger * const logger) {
                *data = build_table_in_proof(enum_vars, determined_vars, accept, selector_name, comment, state, logger);
                if (! data->has_value())
                    inference.infer(logger, FalseLiteral{}, JustifyUsingRUP{Hint_{owner}}, ExplicitReason{ReasonLiterals{}});
            },
            InitialiserPriority::Expensive);

        propagators.install(
            owner,
            [data = data, owner = owner](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
                if (data->has_value())
                    return propagate_extensional(data->value(), state, inference, logger, Hint_{owner});
                else
                    return PropagatorState::DisableUntilBacktrack;
            },
            triggers);
    }
}

#endif
