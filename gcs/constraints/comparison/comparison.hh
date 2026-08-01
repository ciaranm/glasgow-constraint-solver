#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_COMPARISON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_COMPARISON_HH

#include <gcs/constraint.hh>
#include <gcs/constraints/innards/reified_state.hh>
#include <gcs/innards/literal.hh>
#include <gcs/integer.hh>
#include <gcs/reification.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

#include <optional>

namespace gcs
{
    /**
     * \brief General implementation for LessThan, LessThanIf, LessThanIff, etc.
     *
     * \ingroup Constraints
     * \ingroup Innards
     * \sa LessThan
     * \sa LessThanIf
     * \sa LessThanIff
     * \sa LessThanEqual
     * \sa LessThanEqualIff
     * \sa GreaterThan
     * \sa GreaterThanIff
     * \sa GreaterThanEqualIff
     * \sa GreaterThanEqual
     */
    class ReifiedCompareLessThanOrMaybeEqual : public Constraint
    {
    private:
        IntegerVariableID _v1, _v2;
        ReificationCondition _reif_cond;
        bool _or_equal;
        bool _vars_swapped;
        std::optional<Integer> _v1_is_constant, _v2_is_constant;
        innards::EvaluatedReificationCondition _evaluated_cond = innards::evaluated_reif::Deactivated{};

        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &, const innards::State &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

    public:
        explicit ReifiedCompareLessThanOrMaybeEqual(
            const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool or_equal, bool vars_swapped = false);

        /**
         * \name Posted arguments, for presolvers.
         *
         * These read back the constraint exactly as it was constructed, so that
         * a presolver enumerating a Problem (see Problem::each_constraint_of_type)
         * can recognise a shape it knows how to improve upon --- for example,
         * `x <= y + d`, where the offset is a view, is a difference constraint.
         * They are deliberately the constructor's arguments and nothing else: no
         * prepare()-time snapshot is exposed, because a presolver runs with a
         * State and can ask that for current bounds itself.
         *
         * Note that this is the *normalised* form: the whole family is stored as
         * `left <` or `left <=` `right`, so GreaterThan(a, b) reads back as
         * left = b, right = a. (The `vars_swapped` flag that remembers which way
         * round it was posted is not exposed: it only affects the constraint's
         * .scp spelling, and no presolver has any use for it.) Because clone()
         * --- which is what Problem stores --- returns a
         * ReifiedCompareLessThanOrMaybeEqual whatever the derived type was, the
         * reification condition and or_equal(), not the C++ type, are what
         * distinguish LessThan from LessThanEqualIff and the rest.
         *
         * @{
         */

        /**
         * \brief The operand on the smaller side of the comparison, as posted,
         * which may be a constant or a view.
         */
        [[nodiscard]] auto left_variable() const -> IntegerVariableID
        {
            return _v1;
        }

        /**
         * \brief The operand on the larger side of the comparison, as posted,
         * which may be a constant or a view.
         */
        [[nodiscard]] auto right_variable() const -> IntegerVariableID
        {
            return _v2;
        }

        /**
         * \brief Is this the `<=` form (rather than the `<` form)?
         */
        [[nodiscard]] auto or_equal() const -> bool
        {
            return _or_equal;
        }

        /**
         * \brief The reification condition, as posted: reif::MustHold for a
         * plain LessThan, reif::If for the `If` form, and so on.
         */
        [[nodiscard]] auto reification_condition() const GCS_LIFETIME_BOUND -> const ReificationCondition &
        {
            return _reif_cond;
        }

        ///@}
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
        [[nodiscard]] virtual auto constraint_type() const -> std::string override;
    };

    /**
     * \brief Constrain that `v1 < v2`.
     *
     * \ingroup Constraints
     */
    class LessThan : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        explicit LessThan(const IntegerVariableID v1, const IntegerVariableID v2);
    };

    /**
     * \brief Constrain that `v1 < v2` if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LessThanIf : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit LessThanIf(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
            ReifiedCompareLessThanOrMaybeEqual(v1, v2, reif::If{cond}, false) {};
    };

    /**
     * \brief Constrain that `v1 <= v2`.
     *
     * \ingroup Constraints
     */
    class LessThanEqual : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit LessThanEqual(const IntegerVariableID v1, const IntegerVariableID v2) :
            ReifiedCompareLessThanOrMaybeEqual(v1, v2, reif::MustHold{}, true) {};
    };

    /**
     * \brief Constrain that `v1 > v2`.
     *
     * \ingroup Constraints
     */
    class GreaterThan : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        explicit GreaterThan(const IntegerVariableID v1, const IntegerVariableID v2);
    };

    /**
     * \brief Constrain that `v1 > v2` if `cond` holds.
     *
     * \ingroup Constraints
     */
    class GreaterThanIf : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit GreaterThanIf(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
            ReifiedCompareLessThanOrMaybeEqual(v2, v1, reif::If{cond}, false, true) {};
    };

    /**
     * \brief Constrain that `v1 >= v2`.
     *
     * \ingroup Constraints
     */
    class GreaterThanEqual : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit GreaterThanEqual(const IntegerVariableID v1, const IntegerVariableID v2) :
            ReifiedCompareLessThanOrMaybeEqual(v2, v1, reif::MustHold{}, true, true) {};
    };

    /**
     * \brief Constrain that `v1 < v2` if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LessThanIff : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit LessThanIff(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
            ReifiedCompareLessThanOrMaybeEqual(v1, v2, reif::Iff{cond}, false) {};
    };

    /**
     * \brief Constrain that `v1 <= v2` if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LessThanEqualIf : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit LessThanEqualIf(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
            ReifiedCompareLessThanOrMaybeEqual(v1, v2, reif::If{cond}, true) {};
    };

    /**
     * \brief Constrain that `v1 <= v2` if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LessThanEqualIff : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit LessThanEqualIff(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
            ReifiedCompareLessThanOrMaybeEqual(v1, v2, reif::Iff{cond}, true) {};
    };

    /**
     * \brief Constrain that `v1 > v2` if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class GreaterThanIff : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit GreaterThanIff(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
            ReifiedCompareLessThanOrMaybeEqual(v2, v1, reif::Iff{cond}, false, true) {};
    };

    /**
     * \brief Constrain that `v1 >= v2` if `cond` holds.
     *
     * \ingroup Constraints
     */
    class GreaterThanEqualIf : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit GreaterThanEqualIf(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
            ReifiedCompareLessThanOrMaybeEqual(v2, v1, reif::If{cond}, true, true) {};
    };

    /**
     * \brief Constrain that `v1 >= v2` if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class GreaterThanEqualIff : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit GreaterThanEqualIff(const IntegerVariableID v1, const IntegerVariableID v2, IntegerVariableCondition cond) :
            ReifiedCompareLessThanOrMaybeEqual(v2, v1, reif::Iff{cond}, true, true) {};
    };
}

#endif
