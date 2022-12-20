/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_COMPARISON_HH

#include <gcs/constraint.hh>
#include <gcs/literal.hh>
#include <gcs/variable_id.hh>

namespace gcs
{
    namespace innards
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
        class CompareLessThanReif : public Constraint
        {
        private:
            IntegerVariableID _v1, _v2;
            Literal _cond;
            bool _full_reif;
            bool _or_equal;

        public:
            explicit CompareLessThanReif(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond, bool full_reif, bool or_equal);

            virtual auto describe_for_proof() -> std::string override;
            virtual auto install(innards::Propagators &, innards::State &) && -> void override;
            virtual auto clone() const -> std::unique_ptr<Constraint> override;
        };
    }

    /**
     * \brief Constrain that `v1 < v2`.
     *
     * \ingroup Constraints
     */
    class LessThan : public innards::CompareLessThanReif
    {
    public:
        inline explicit LessThan(const IntegerVariableID v1, const IntegerVariableID v2) :
            CompareLessThanReif(v1, v2, TrueLiteral{}, true, false){};
    };

    /**
     * \brief Constrain that `v1 < v2` if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LessThanIf : public innards::CompareLessThanReif
    {
    public:
        inline explicit LessThanIf(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            CompareLessThanReif(v1, v2, cond, false, false){};
    };

    /**
     * \brief Constrain that `v1 <= v2`.
     *
     * \ingroup Constraints
     */
    class LessThanEqual : public innards::CompareLessThanReif
    {
    public:
        inline explicit LessThanEqual(const IntegerVariableID v1, const IntegerVariableID v2) :
            CompareLessThanReif(v1, v2, TrueLiteral{}, true, true){};
    };

    /**
     * \brief Constrain that `v1 > v2`.
     *
     * \ingroup Constraints
     */
    class GreaterThan : public innards::CompareLessThanReif
    {
    public:
        inline explicit GreaterThan(const IntegerVariableID v1, const IntegerVariableID v2) :
            CompareLessThanReif(v2, v1, TrueLiteral{}, true, false){};
    };

    /**
     * \brief Constrain that `v1 >= v2`.
     *
     * \ingroup Constraints
     */
    class GreaterThanEqual : public innards::CompareLessThanReif
    {
    public:
        inline explicit GreaterThanEqual(const IntegerVariableID v1, const IntegerVariableID v2) :
            CompareLessThanReif(v2, v1, TrueLiteral{}, true, true){};
    };

    /**
     * \brief Constrain that `v1 < v2` if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LessThanIff : public innards::CompareLessThanReif
    {
    public:
        inline explicit LessThanIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            CompareLessThanReif(v1, v2, cond, true, false){};
    };

    /**
     * \brief Constrain that `v1 <= v2` if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class LessThanEqualIff : public innards::CompareLessThanReif
    {
    public:
        inline explicit LessThanEqualIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            CompareLessThanReif(v1, v2, cond, true, true){};
    };

    /**
     * \brief Constrain that `v1 > v2` if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class GreaterThanIff : public innards::CompareLessThanReif
    {
    public:
        inline explicit GreaterThanIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            CompareLessThanReif(v2, v1, cond, true, false){};
    };

    /**
     * \brief Constrain that `v1 >= v2` if and only if `cond` holds.
     *
     * \ingroup Constraints
     */
    class GreaterThanEqualIff : public innards::CompareLessThanReif
    {
    public:
        inline explicit GreaterThanEqualIff(const IntegerVariableID v1, const IntegerVariableID v2, Literal cond) :
            CompareLessThanReif(v2, v1, cond, true, true){};
    };
}

#endif
