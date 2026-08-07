#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_SCAFFOLDING_SCOPE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_PROOF_SCAFFOLDING_SCOPE_HH

#include <gcs/innards/proofs/proof_logger-fwd.hh>

namespace gcs::innards
{
    /**
     * \brief A derivation's working, one proof level below the caller's, and
     * deleted again on the way out.
     *
     * The pattern this replaces was written out six times, and every copy of it
     * says the same thing: everything between here and the line the routine
     * finally claims exists only to reach that line, so at Top not one of those
     * constraints would ever be deleted and each would tax every later unhinted
     * RUP (issue #666). One level *deeper* than the caller's rather than plain
     * Temporary, because a caller inside a JustifyExplicitly is already using
     * its own Temporary depth and would lose it to the forget.
     *
     * Constructing enters `caller + 1`; destruction restores the caller's level
     * and forgets `caller + 2`, which is where the working's Temporary lines
     * land. A routine with several ways out therefore no longer needs a
     * give-it-back lambda or a gave-up flag on each of them, and a
     * ProofError thrown from inside no longer leaves the logger at the deeper
     * level.
     *
     * \sa restore, for the ordering a routine pinning at the *caller's* level
     * has to observe.
     *
     * \ingroup Innards
     */
    class ProofScaffoldingScope
    {
    private:
        ProofLogger & _logger;
        int _saved;
        bool _restored = false;

    public:
        explicit ProofScaffoldingScope(ProofLogger &);
        ~ProofScaffoldingScope();

        ProofScaffoldingScope(const ProofScaffoldingScope &) = delete;
        auto operator=(const ProofScaffoldingScope &) -> ProofScaffoldingScope & = delete;

        /**
         * \brief Go back to the caller's level early, with the working still
         * alive to be cited.
         *
         * For a routine whose result is emitted at whatever ProofLevel its
         * caller asked for: that emit has to happen at the caller's level, and
         * while the working it cites is still there for VeriPB to resolve the
         * reference against. So restore, emit, and let the destructor forget. A
         * routine claiming its result at Top does not need this --- Top is
         * depth zero whatever the active level is.
         *
         * Idempotent, and the destructor does it if nothing else has.
         */
        auto restore() -> void;
    };
}

#endif
