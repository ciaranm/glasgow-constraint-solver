#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH

#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_model-fwd.hh>
#include <gcs/lifetime.hh>

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
        std::optional<std::string> s_expr_file;        ///< Filename for the s-expression verified definition
    };

    /**
     * \brief Mode setting for annotated assertions. Each option involves successively less
     * justification.
     */
    enum class AssertionLevel
    {
        Off = 0,      /// Justify everything; no annotated assertions
        Definitions,  /// Justify backtracking, links, definitions; assert inferences
        Links,        /// Justify backtracking; assert inferences & links; omit definitions
        Inferences,   /// Assert backtracking & inferences; omit links & definitions
        Backtracking, /// Assert backtracking only; omit everything else
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
        explicit ProofOptions(const ProofFileNames &);
        ProofOptions(const ProofOptions &) = default;

        ProofFileNames proof_file_names;           ///< Filenames for OPB, proof, and mapping files
        bool verbose_names = true;                 ///< Use verbose names in proofs?
        bool always_use_full_encoding = false;     ///< Always write the full variable encoding to the OPB file
        bool use_compact_boolean_encoding = false; ///< Drop the trivial constant boundary literals (ge_lower, ge_ub+1) from eq-atom definitions
        AssertionLevel assertion_level = AssertionLevel::Off;
        bool assertion_level_set_explicitly = false; ///< Was assertion_level set in code (so it overrides the env var)?

        /// Write annotated assertions instead of full justifications.
        ProofOptions & set_assertion_level(AssertionLevel a = AssertionLevel::Inferences)
        {
            assertion_level = a;
            assertion_level_set_explicitly = true;
            return *this;
        }
        /// Always write the full variable encoding to the OPB file.
        ProofOptions & enable_full_encoding(bool e = true)
        {
            always_use_full_encoding = e;
            return *this;
        }
        /// Use the compact boolean encoding: define an eq atom at the variable's
        /// lower (resp. upper) bound as eq <=> ~ge(v+1) (resp. eq <=> ge(v)),
        /// dropping the trivially-true ge(lower) and trivially-false ge(ub+1)
        /// literals. With this off (the default) every eq atom, including those
        /// at the bounds, is defined as eq <=> ge(v) & ~ge(v+1), so those
        /// constant boundary literals are materialised -- matching cake_pb_cp's
        /// eager encoding.
        ProofOptions & set_compact_boolean_encoding(bool c = true)
        {
            use_compact_boolean_encoding = c;
            return *this;
        }
        /// Set whether to use verbose names in proofs.
        ProofOptions & set_verbose_names(bool v)
        {
            verbose_names = v;
            return *this;
        }
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

        /**
         * \brief The proof logger, for writing proof steps.
         *
         * \warning This is a pointer into this Proof, and is valid only for as
         * long as the Proof is alive.
         */
        [[nodiscard]] auto logger() GCS_LIFETIME_BOUND -> innards::ProofLogger *;

        /**
         * \brief The proof model, for writing OPB-level definitions.
         *
         * \warning This is a pointer into this Proof, and is valid only for as
         * long as the Proof is alive.
         */
        [[nodiscard]] auto model() GCS_LIFETIME_BOUND -> innards::ProofModel *;
    };
}

#endif
