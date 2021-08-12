/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_PROOF_HH 1

#include <gcs/variable_id.hh>
#include <gcs/justification.hh>
#include <gcs/literal.hh>
#include <gcs/state-fwd.hh>

#include <exception>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace gcs
{
    class ProofError :
        public std::exception
    {
        private:
            std::string _wat;

        public:
            explicit ProofError(const std::string &);

            virtual auto what() const noexcept -> const char * override;
    };

    class Proof
    {
        private:
            struct Imp;
            std::unique_ptr<Imp> _imp;

            auto proof_variable(const LiteralFromIntegerVariable &) const -> const std::string &;
            auto proof_variable(const LiteralFromBooleanVariable &) const -> const std::string &;
            auto proof_variable(const Literal &) const -> const std::string &;

        public:
            explicit Proof(const std::string & opb_file, const std::string & proof_file);
            ~Proof();

            auto operator= (const Proof &) -> Proof & = delete;
            Proof(const Proof &) = delete;

            Proof(Proof &&);
            auto operator= (Proof &&) -> Proof &;

            // OPB-related output
            auto posting(const std::string &) -> void;
            auto create_integer_variable(IntegerVariableID, Integer, Integer, const std::optional<std::string> &, bool need_ge) -> void;
            auto cnf(const Literals &) -> void;

            // Proof-related output
            auto start_proof() -> void;

            auto solution(const State &) -> void;
            auto backtrack(const State &) -> void;
            auto assert_contradiction() -> void;

            auto infer(const State & state, const Literal & lit, Justification why) -> void;
    };
}

#endif