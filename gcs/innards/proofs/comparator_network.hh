#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_COMPARATOR_NETWORK_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_PROOFS_COMPARATOR_NETWORK_HH

#include <gcs/innards/proofs/proof_line.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_only_variables.hh>
#include <gcs/integer.hh>

#include <string>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief A proof-only bit-encoded integer: `width` fresh flags, read as
     * `sum_t 2^t * bits[t]`.
     *
     * Nothing in the model mentions a wire. It exists only between the `red`
     * that introduces its bits and the deletion that removes them, which is
     * what lets a propagator sort its tasks inside a proof without the OPB
     * acquiring a sorting network --- or, for that matter, a time index.
     *
     * Bits rather than ProofModel::create_proof_only_integer_variable_in_proof,
     * which is a *model*-side call and so unavailable to a propagator: a wire
     * introduced during search cannot be a model variable, and does not need to
     * be, every step below being cutting planes over the bits.
     *
     * \ingroup Innards
     */
    struct ProofWire
    {
        std::vector<ProofFlag> bits;
    };

    /**
     * \brief One comparator's outputs, and the rows saying what they are.
     *
     * `selector` is true exactly when `a <= b`, so `lo` takes `a` and `hi`
     * takes `b`; each output is muxed bitwise on it. The four record rows are
     * the conditional statements a later lemma consumes --- `lo_ge_a` is
     * `selector -> lo >= a`, and so on --- each one `pol`, built by multiplying
     * the bit-`t` mux clause by `2^t` and summing.
     *
     * The guard coefficient on a record row comes out at `span` (the largest
     * value a wire of this width can take) and is deliberately left there:
     * a transfer lemma adds two of them and divides by a separation row's
     * guard coefficient, which is a clean one only while `2 * span` does not
     * exceed it.
     *
     * \ingroup Innards
     */
    struct Comparator
    {
        ProofFlag selector;
        ProofWire lo, hi;

        /// `selector -> b >= a`, and `~selector -> a >= b + 1`.
        ProofLine forward, reverse;

        /// The muxed record rows, `guard -> output (>= or <=) input`.
        ProofLine lo_ge_a, lo_le_a, lo_ge_b, lo_le_b;
        ProofLine hi_ge_b, hi_le_b, hi_ge_a, hi_le_a;
    };

    /**
     * \brief Builds proof-only comparator networks over bit-encoded integer
     * wires.
     *
     * The construction is the one issue #730 verified in simulation: wires
     * introduced by redundance, sorted by a network of comparators, with order
     * facts carried across each comparator and telescoped at the end. Its
     * distinguishing property is that it is *duration-magnitude invariant* ---
     * cost depends on the number of wires and only logarithmically on their
     * range --- which is what makes it the certificate of choice where a
     * time-indexed re-encoding would be too wide.
     *
     * Every step is emitted at the level the network was built with, so a
     * caller that wants the whole thing gone on backtracking asks for
     * ProofLevel::Temporary and a caller amortising it over many firings asks
     * for ProofLevel::Top.
     *
     * \ingroup Innards
     */
    class ComparatorNetwork
    {
    private:
        ProofLogger & _logger;
        int _width;
        ProofLevel _level;
        Integer _span, _big;
        long long _counter = 0;

        [[nodiscard]] auto next_name(const std::string & stem) -> std::string;

    public:
        /**
         * `width` bits per wire, which must be enough for every value the
         * caller pins or bounds. `big` is the guard coefficient every
         * conditional row carries; it has to dominate twice a wire's span, so
         * that a transfer lemma's division comes out at one, and the caller's
         * own rows have to be raised to it (see \ref raise_guard).
         */
        explicit ComparatorNetwork(ProofLogger &, int width, ProofLevel);

        [[nodiscard]] auto width() const -> int;
        [[nodiscard]] auto span() const -> Integer;
        [[nodiscard]] auto big() const -> Integer;

        /// A fresh wire, its bits unconstrained until something pins or defines
        /// them.
        [[nodiscard]] auto fresh_wire(const std::string & stem) -> ProofWire;

        /// `sign * wire` as pseudo-Boolean terms, for building a row about it.
        [[nodiscard]] auto terms(const ProofWire &, Integer sign) const -> WPBSum;

        /// The same, appended to a sum already under construction, which is
        /// what a row mentioning several wires needs.
        auto add_terms(WPBSum &, const ProofWire &, Integer sign) const -> void;

        /**
         * Fix a fresh wire to a constant, one `red` per bit. The witness is
         * single-variable and the wire is fresh, so both proofgoals autoprove
         * and no subproof is needed.
         */
        auto pin(const ProofWire &, Integer value) -> void;

        /**
         * Introduce a comparator over two wires already in play: a selector
         * reifying `a <= b` by two `red`s, four bitwise muxes per output bit,
         * and the eight conditional record rows those give by `pol`.
         */
        [[nodiscard]] auto compare(const ProofWire & a, const ProofWire & b, const std::string & stem) -> Comparator;
    };
}

#endif
