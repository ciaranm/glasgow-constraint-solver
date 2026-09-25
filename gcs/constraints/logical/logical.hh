#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LOGICAL_LOGICAL_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_LOGICAL_LOGICAL_HH 1

#include <gcs/constraint.hh>
#include <gcs/innards/literal.hh>
#include <gcs/innards/state.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <cstddef>
#include <optional>
#include <vector>

namespace gcs
{
    namespace innards
    {
        /**
         * \brief The default number of literals at and above which a clause
         * watches two of its literals rather than scanning them all, used when
         * a constraint is posted without an explicit threshold.
         *
         * A clause here is an And, Or or OrIf whose condition is decided at
         * install in the direction that leaves only "at least one literal"
         * (equivalently, "not every literal of the And form") to enforce: every
         * unreified Or, for instance. The scan walks every literal decided so
         * far on every wake, which is cheap for a short clause, but on a long
         * one is the whole cost of the constraint. Watching costs more per
         * wake but wakes far less. See dev_docs/refined-triggers.md.
         *
         * The per-constraint threshold (with_watch_threshold()) is the
         * intended interface; this default is overridable via the
         * GCS_CLAUSE_WATCH_THRESHOLD environment variable, which is how the test
         * suite sweeps both code paths (0 = always watch, a huge value = always
         * scan).
         */
        [[nodiscard]] auto default_clause_watch_threshold() -> std::size_t;
    }

    /**
     * \brief Constrain that each of the literals is true (or variables are
     * non-zero) if and only if the reification variable holds.
     *
     * \ingroup Constraints
     */
    class And : public Constraint
    {
    private:
        const innards::Literals _lits;
        const innards::Literal _full_reif;
        innards::LiteralIs _reif_state = innards::LiteralIs::Undecided;
        std::optional<std::size_t> _watch_threshold = std::nullopt;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        // Equivalent to And([var != 0 : var in vars], full_reif != 0)
        explicit And(const std::vector<IntegerVariableID> & vars, const IntegerVariableID & full_reif);

        // Equivalent to And([var != 0 : var in vars], true)
        explicit And(const std::vector<IntegerVariableID> & vars);

        explicit And(innards::Literals, const innards::Literal &);

        /**
         * \brief Set the number of literals at and above which this
         * constraint, when its reification is decided false at install, so
         * that it says only that not every literal holds, watches two literals
         * rather than scanning them all; unset means
         * innards::default_clause_watch_threshold().
         */
        auto with_watch_threshold(std::optional<std::size_t> threshold) -> And &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief Constrain that at least one of the literals is true (or variables
     * are non-zero) if and only if the reification variable holds.
     *
     * \ingroup Constraints
     */
    class Or : public Constraint
    {
    private:
        const innards::Literals _lits;
        const innards::Literal _full_reif;
        innards::LiteralIs _reif_state = innards::LiteralIs::Undecided;
        std::optional<std::size_t> _watch_threshold = std::nullopt;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        // Equivalent to Or([var != 0 : var in vars], full_reif != 0)
        explicit Or(const std::vector<IntegerVariableID> & vars, const IntegerVariableID & full_reif);

        // Equivalent to Or([var != 0 : var in vars], true)
        explicit Or(const std::vector<IntegerVariableID> & vars);

        explicit Or(innards::Literals, const innards::Literal &);

        /**
         * \brief Set the number of literals at and above which this
         * constraint, when its reification is decided true at install, so that
         * it is a clause, watches two literals rather than scanning them all;
         * unset means innards::default_clause_watch_threshold().
         */
        auto with_watch_threshold(std::optional<std::size_t> threshold) -> Or &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief Constrain that if the condition holds, each of the literals is
     * true (or variables are non-zero).
     *
     * The half-reified form of And: nothing is required of the literals when
     * the condition is false, and the literals all holding says nothing about
     * the condition.
     *
     * \ingroup Constraints
     */
    class AndIf : public Constraint
    {
    private:
        const innards::Literals _lits;
        const innards::Literal _cond;
        innards::LiteralIs _cond_state = innards::LiteralIs::Undecided;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        // Equivalent to AndIf([var != 0 : var in vars], cond != 0)
        explicit AndIf(const std::vector<IntegerVariableID> & vars, const IntegerVariableID & cond);

        explicit AndIf(innards::Literals, const innards::Literal &);

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief Constrain that if the condition holds, at least one of the
     * literals is true (or variables are non-zero).
     *
     * The half-reified form of Or, and so the clause `! cond \/ lits`: nothing
     * is required of the literals when the condition is false, and a literal
     * holding says nothing about the condition.
     *
     * \ingroup Constraints
     */
    class OrIf : public Constraint
    {
    private:
        const innards::Literals _lits;
        const innards::Literal _cond;
        innards::LiteralIs _cond_state = innards::LiteralIs::Undecided;
        std::optional<std::size_t> _watch_threshold = std::nullopt;

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        // Equivalent to OrIf([var != 0 : var in vars], cond != 0)
        explicit OrIf(const std::vector<IntegerVariableID> & vars, const IntegerVariableID & cond);

        explicit OrIf(innards::Literals, const innards::Literal &);

        /**
         * \brief Set the number of literals at and above which this
         * constraint, when its condition is decided true at install, so that
         * it is a clause, watches two literals rather than scanning them all;
         * unset means innards::default_clause_watch_threshold().
         */
        auto with_watch_threshold(std::optional<std::size_t> threshold) -> OrIf &;

        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };
}

#endif
