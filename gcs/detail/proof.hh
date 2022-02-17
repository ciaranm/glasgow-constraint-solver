/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH

#include <gcs/detail/justification.hh>
#include <gcs/detail/linear_utils.hh>
#include <gcs/detail/literal_utils.hh>
#include <gcs/detail/state-fwd.hh>
#include <gcs/linear.hh>
#include <gcs/literal.hh>
#include <gcs/proof_options.hh>
#include <gcs/variable_id.hh>

#include <exception>
#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace gcs
{
    class ProofError : public std::exception
    {
    private:
        std::string _wat;

    public:
        explicit ProofError(const std::string &);

        virtual auto what() const noexcept -> const char * override;
    };

    struct ProofFlag
    {
        unsigned long long index;
        bool positive;
    };

    [[nodiscard]] auto operator!(const ProofFlag &) -> ProofFlag;

    using LiteralFromIntegerVariableOrProofFlag = std::variant<LiteralFromIntegerVariable, ProofFlag>;

    class Proof
    {
    private:
        struct Imp;
        std::unique_ptr<Imp> _imp;

        [[nodiscard]] auto xify(std::string &&) -> std::string;

        auto need_gevar(SimpleIntegerVariableID id, Integer v) -> void;

    public:
        explicit Proof(const ProofOptions &);
        ~Proof();

        auto operator=(const Proof &) -> Proof & = delete;
        Proof(const Proof &) = delete;

        Proof(Proof &&) noexcept;
        auto operator=(Proof &&) noexcept -> Proof &;

        // OPB-related output
        auto posting(const std::string &) -> void;
        auto create_integer_variable(SimpleIntegerVariableID, Integer, Integer, const std::optional<std::string> &,
            bool direct_encoding) -> void;
        [[nodiscard]] auto create_proof_flag(const std::string &) -> ProofFlag;
        auto cnf(const Literals &) -> ProofLine;
        [[nodiscard]] auto at_most_one(const Literals &) -> ProofLine;
        [[nodiscard]] auto pseudoboolean_ge(const WeightedLiterals &, Integer) -> ProofLine;
        auto integer_linear_le(const State &, const SimpleLinear & coeff_vars, Integer value,
            std::optional<LiteralFromIntegerVariableOrProofFlag> half_reif, bool equality) -> ProofLine;

        auto minimise(IntegerVariableID) -> void;

        auto need_proof_variable(const Literal &) -> void;
        auto need_direct_encoding_for(SimpleIntegerVariableID, Integer) -> void;

        // Proof-related output
        auto start_proof(State & initial_state) -> void;

        auto solution(const State &) -> void;
        auto backtrack(const State &) -> void;
        auto assert_contradiction() -> void;

        auto infer(const State & state, const Literal & lit, const Justification & why) -> void;

        auto enter_proof_level(int depth) -> void;
        auto forget_proof_level(int depth) -> void;

        // Writing proof steps from constraints
        auto add_proof_steps(const JustifyExplicitly &, std::vector<ProofLine> & to_delete) -> void;
        auto delete_proof_lines(const std::vector<ProofLine> & to_delete) -> void;
        auto emit_proof_line(const std::string &) -> ProofLine;
        auto emit_proof_comment(const std::string &) -> void;
        [[nodiscard]] auto trail_variables(const State &, Integer coeff) -> std::string;
        [[nodiscard]] auto need_constraint_saying_variable_takes_at_least_one_value(IntegerVariableID) -> ProofLine;
        auto for_each_bit_defining_var(IntegerVariableID var, const std::function<auto(Integer, const std::string &)->void> &) -> void;

        auto create_pseudovariable(SimpleIntegerVariableID, Integer, Integer, const std::optional<std::string> &) -> void;

        [[nodiscard]] auto proof_variable(const Literal &) const -> const std::string &;
        [[nodiscard]] auto proof_variable(const ProofFlag &) const -> const std::string &;
    };
}

#endif
