#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH

#include <gcs/constraint.hh>
#include <gcs/innards/literal.hh>
#include <gcs/reification.hh>
#include <gcs/variable_condition.hh>
#include <gcs/variable_id.hh>

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
        bool _full_reif;
        bool _or_equal;
        bool _vars_swapped;

    public:
        explicit ReifiedCompareLessThanOrMaybeEqual(const IntegerVariableID v1, const IntegerVariableID v2, ReificationCondition cond, bool or_equal, bool vars_swapped = false);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };

    /**
     * \brief Constrain that `v1 < v2`.
     *
     * \ingroup Constraints
     */
    class LessThan : public ReifiedCompareLessThanOrMaybeEqual
    {
    public:
        inline explicit LessThan(const IntegerVariableID v1, const IntegerVariableID v2) :
            ReifiedCompareLessThanOrMaybeEqual(v1, v2, reif::MustHold{}, false) {};
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
        inline explicit GreaterThan(const IntegerVariableID v1, const IntegerVariableID v2) :
            ReifiedCompareLessThanOrMaybeEqual(v2, v1, reif::MustHold{}, false, true) {};
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
