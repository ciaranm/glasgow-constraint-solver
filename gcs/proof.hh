#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH

#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>

#include <memory>
#include <optional>
#include <string>

namespace gcs
{
    /**
     * \brief Options for a Problem telling it how to produce a proof.
     *
     * \sa Problem
     * \ingroup Core
     */
    struct ProofOptions final
    {
        explicit ProofOptions(std::string, std::string);
        explicit ProofOptions(std::string, std::string, bool, bool, bool);
        ProofOptions(const ProofOptions &) = default;

        std::string opb_file;                  ///< Filename for the OPB model
        std::string proof_file;                ///< Filename for the proof file
        bool use_friendly_names = true;        ///< Use verbose names, rather than just x1, x2, etc.
        bool always_use_full_encoding = false; ///< Always write the full variable encoding to the OPB file
        bool use_reasons = true;               ///< Write proofs using reasons rather than guesses
    };

    class Proof
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

    public:
        explicit Proof(const ProofOptions &);
        ~Proof();

        auto operator=(const Proof &) -> Proof & = delete;
        Proof(const Proof &) = delete;

        [[nodiscard]] auto logger() -> innards::ProofLogger *;
        [[nodiscard]] auto model() -> innards::ProofModel *;
    };
}

#endif
