#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_CANONICAL_RUN_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_REGULAR_CANONICAL_RUN_HH

#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/innards/state-fwd.hh>
#include <gcs/integer.hh>
#include <gcs/variable_id.hh>

#include <set>
#include <unordered_map>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Does some word of length `vars.size()`, over the variables'
     * domains in `state`, have two accepting runs through the automaton?
     *
     * Regular's state flags record one accepting run, with an exactly-one per
     * layer. On a word with two, nothing in the OPB says which run the flags
     * follow, so unit propagation from the variables leaves them unassigned and
     * VeriPB rejects the solution line (issue #1203). A deterministic automaton
     * is never ambiguous, and neither is a non-deterministic one in which every
     * accepted word has one accepting run, so this is the test for whether
     * emit_regular_canonical_run() is needed.
     *
     * Runs a product of the automaton with itself, one layer per variable, over
     * the statically live states only, carrying a bit for whether the two runs
     * have diverged yet. A deterministic automaton returns at once.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto regular_is_ambiguous(const std::vector<IntegerVariableID> & vars,
        const std::vector<std::unordered_map<Integer, std::set<long>>> & transitions, const std::vector<long> & final_states, const State & state)
        -> bool;

    /**
     * \brief Pin Regular's state flags to one canonical accepting run, so that
     * unit propagation from the variables alone sets every one of them.
     *
     * For an ambiguous automaton (see regular_is_ambiguous()). Leaves the OPB
     * alone, and adds nothing to the solution lines. Emits at ProofLevel::Top,
     * and must run before any other proof line mentions the state flags. The
     * derivation is in dev_docs/regular.md, "Ambiguous automata".
     *
     * \ingroup Innards
     */
    auto emit_regular_canonical_run(ProofLogger & logger, const std::vector<IntegerVariableID> & vars, long num_states,
        const std::vector<std::unordered_map<Integer, std::set<long>>> & transitions, const std::vector<long> & final_states,
        const std::vector<std::vector<ProofFlag>> & state_flags, const State & state) -> void;
}

#endif
