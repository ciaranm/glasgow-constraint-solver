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
     * \brief Filenames for a ProofOptions.
     *
     * \sa ProofOptions
     * \ingroup Core
     */
    struct ProofFileNames final
    {
        /**
         * Construct a ProofFileNames, using the specifed prefix with ".opb", etc appended.
         */
        explicit ProofFileNames(const std::string &);

        std::string opb_file;                          ///< Filename for the OPB model
        std::string proof_file;                        ///< Filename for the proof file
        std::optional<std::string> variables_map_file; ///< Filename for variables mapping file
    };

    /**
     * \brief Options for a Problem telling it how to produce a proof.
     *
     * \sa Problem
     * \ingroup Core
     */
    struct ProofOptions final
    {
        explicit ProofOptions(const std::string &);
        explicit ProofOptions(const ProofFileNames &, bool, bool);
        ProofOptions(const ProofOptions &) = default;

        ProofFileNames proof_file_names;       ///< Filenames for OPB, proof, and mapping files
        bool verbose_names = true;             ///< Use verbose names in proofs?
        bool always_use_full_encoding = false; ///< Always write the full variable encoding to the OPB file
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
