#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_GRAPH_RULES_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INNARDS_GRAPH_RULES_HH

#include <gcs/constraint_id.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/innards/reason.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <string>
#include <string_view>
#include <variant>
#include <vector>

namespace gcs::innards::hints
{
    /**
     * \brief The graph-structure rules' assertion hint: just the owning
     * constraint, no subhint.
     *
     * \ingroup Innards
     */
    struct GraphRules
    {
        ConstraintID originator;
        static constexpr std::string_view hint_name = "graphrules";
    };
}

/**
 * \brief The counting rules that turn a reachable subgraph into a tree or a
 * path: "at most this many of these edges", and "this node is selected",
 * each optionally conditional on where the root or an endpoint went.
 *
 * Tree, DTree, Path and DPath are all a reachability child plus a cardinality
 * child plus a handful of these, so the rows and the propagation live here
 * once. A rule's row is labelled `c[id][role]` and every inference below is a
 * plain RUP against exactly that row, which is why `role` has to name
 * everything that varies: the node it is about, and which degree it counts.
 *
 * \ingroup Innards
 */
namespace gcs::innards::graph_rules
{
    /**
     * \brief `conds` all hold implies at most `limit` of `vars` are 1.
     *
     * A variable appearing twice in `vars` counts twice, which is what a self
     * loop means for an undirected degree.
     */
    struct AtMost
    {
        std::string role;
        std::vector<IntegerVariableID> vars;
        Integer limit;
        std::vector<IntegerVariableCondition> conds;
    };

    /**
     * \brief `conds` all hold implies `var` is 1.
     */
    struct Selected
    {
        std::string role;
        IntegerVariableID var;
        std::vector<IntegerVariableCondition> conds;
    };

    using Rule = std::variant<AtMost, Selected>;

    /**
     * \brief Write one OPB row per rule, half-reified on its conditions.
     */
    auto define(ProofModel & model, const ConstraintID & id, const std::vector<Rule> & rules) -> void;

    /**
     * \brief Every variable a rule reads, so a caller can install triggers on
     * exactly what it looks at. Duplicates are possible and harmless.
     */
    auto variables_of(const std::vector<Rule> & rules) -> std::vector<IntegerVariableID>;

    /**
     * \brief Enforce the rules, forwards and backwards.
     *
     * Forwards, a rule whose conditions all hold pushes: an AtMost that is full
     * puts every undecided variable out, and a Selected puts its variable in.
     * Backwards, a rule that would be broken rules out the one condition still
     * undecided --- which is how "the start of a path has no edge coming in"
     * takes a node out of the start variable's domain rather than waiting for
     * the start to be decided. With more than one condition undecided there is
     * nothing to name, so nothing is inferred.
     */
    template <typename Hint_, typename Inference_>
    auto propagate(const std::vector<Rule> & rules, const Hint_ & hint, const State & state, Inference_ & inference, ProofLogger * const logger)
        -> void
    {
        // The hint comes from the caller rather than from here: an assertion
        // annotation names the constraint an external justifier has to reason
        // about, which is the tree or the path the model posted, not this shared
        // helper.
        auto justify = JustifyUsingRUP{hint};

        // A rule's conditions, sorted into "cannot fire", "holds, and here is the
        // literal to blame it on", and "still open". Returns false if the rule is
        // dead for this state.
        auto conditions = [&](const std::vector<IntegerVariableCondition> & conds, ReasonLiterals & reason,
                              std::vector<IntegerVariableCondition> & open) -> bool {
            for (const auto & c : conds)
                switch (state.test_literal(c)) {
                case LiteralIs::DefinitelyFalse: return false;
                case LiteralIs::DefinitelyTrue: reason.push_back(c); break;
                case LiteralIs::Undecided: open.push_back(c); break;
                }
            return true;
        };

        for (const auto & rule : rules) {
            if (const auto * at_most = std::get_if<AtMost>(&rule)) {
                ReasonLiterals reason;
                std::vector<IntegerVariableCondition> open;
                if (! conditions(at_most->conds, reason, open))
                    continue;

                // Which variables are already in, and which are still open. A
                // variable fixed to 1 is part of every reason below; one fixed to
                // 0 is irrelevant either way.
                ReasonLiterals ones;
                std::vector<IntegerVariableID> undecided;
                for (const auto & v : at_most->vars) {
                    auto value = state.optional_single_value(v);
                    if (value && *value == 1_i)
                        ones.push_back(v == 1_i);
                    else if (! value)
                        undecided.push_back(v);
                }

                if (Integer(static_cast<long long>(ones.size())) < at_most->limit)
                    continue;

                auto full_reason = reason;
                full_reason.insert(full_reason.end(), ones.begin(), ones.end());

                if (open.empty()) {
                    if (Integer(static_cast<long long>(ones.size())) > at_most->limit)
                        inference.contradiction(logger, justify, ExplicitReason{full_reason});
                    // Full, so everything still open has to go out.
                    for (const auto & v : undecided)
                        inference.infer(logger, v == 0_i, justify, ExplicitReason{full_reason});
                }
                else if (open.size() == 1 && Integer(static_cast<long long>(ones.size())) > at_most->limit) {
                    // The rule cannot hold, and exactly one condition is left to
                    // take the blame.
                    inference.infer(logger, ! open.front(), justify, ExplicitReason{full_reason});
                }
            }
            else {
                const auto & selected = std::get<Selected>(rule);
                ReasonLiterals reason;
                std::vector<IntegerVariableCondition> open;
                if (! conditions(selected.conds, reason, open))
                    continue;

                auto value = state.optional_single_value(selected.var);
                if (open.empty()) {
                    if (! (value && *value == 1_i))
                        inference.infer(logger, selected.var == 1_i, justify, ExplicitReason{reason});
                }
                else if (open.size() == 1 && value && *value == 0_i) {
                    auto full_reason = reason;
                    full_reason.push_back(selected.var == 0_i);
                    inference.infer(logger, ! open.front(), justify, ExplicitReason{full_reason});
                }
            }
        }
    }
}

#endif
