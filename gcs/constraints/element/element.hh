#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ELEMENT_ELEMENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ELEMENT_ELEMENT_HH

#include <gcs/array_param.hh>
#include <gcs/consistency.hh>
#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <utility>
#include <variant>
#include <vector>

namespace gcs
{
    namespace innards
    {
        template <typename E_, unsigned n_>
        struct MakeNDVector;

        template <typename E_>
        struct MakeNDVector<E_, 1>
        {
            using Type = std::vector<E_>;
        };

        template <typename E_, unsigned n_>
        struct MakeNDVector
        {
            using Type = std::vector<typename MakeNDVector<E_, n_ - 1>::Type>;
        };
    }

    /**
     * \brief The consistency levels supported by the Element family: generalised
     * arc consistency, or bounds consistency. The variable-array forms (Element,
     * Element2D) default to GAC; the constant-array forms default to BC.
     *
     * \ingroup Consistency
     */
    using ElementConsistency = std::variant<consistency::GAC, consistency::BC>;

    template <typename EntryType_, unsigned dimensions_>
    class NDimensionalElement : public Constraint
    {
    public:
        using ArrayData = typename innards::MakeNDVector<EntryType_, dimensions_>::Type;
        // The handle callers pass: an owned container, a shared_ptr<const ...> to
        // reuse one array across constraints, or a borrowed pointer to storage
        // the caller keeps alive (the latter matches the old `Array *` API).
        using Array = ArrayParam<ArrayData>;
        using IndexVariables = std::vector<IntegerVariableID>;
        using IndexStarts = std::vector<Integer>;

    protected:
        IntegerVariableID _result_var;
        IndexVariables _index_vars;
        IndexStarts _index_starts;
        Array _array;
        bool _bounds_only;
        bool _array_has_nonconstants = false;
        bool _has_empty_dim = false;

    private:
        virtual auto prepare(innards::Propagators &, innards::State &, innards::ProofModel * const) -> bool override;
        virtual auto define_proof_model(innards::ProofModel &) -> void override;
        virtual auto install_propagators(innards::Propagators &) -> void override;

        // install_propagators dispatches here on the concrete type of the index
        // variables (all-Simple / all-View / all-constant, else the mixed
        // IntegerVariableID vector), so the hot per-element iteration is specialised
        // at install time rather than branching per call. \p IndexVec_ is one of the
        // alternatives of innards::as_homogeneous()'s result.
        template <typename IndexVec_>
        auto install_propagators_impl(innards::Propagators & propagators, const IndexVec_ & index_vars) -> void;

    protected:
        explicit NDimensionalElement(IntegerVariableID result_var, IndexVariables, IndexStarts, Array, bool bounds_only);

    public:
        /// Select the consistency level: consistency::GAC or consistency::BC.
        /// This selects propagation strength only and never changes the OPB
        /// encoding. Requesting any other level is a compile-time error.
        auto with_consistency(ElementConsistency level) -> NDimensionalElement &
        {
            _bounds_only = std::holds_alternative<consistency::BC>(level);
            return *this;
        }

        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_expr(const innards::ProofModel * const) const -> innards::SExpr override;
    };

    class Element : public NDimensionalElement<IntegerVariableID, 1>
    {
    public:
        explicit Element(IntegerVariableID var, IntegerVariableID zero_idx, Array array) :
            NDimensionalElement(var, {{zero_idx}}, {{0_i}}, std::move(array), false)
        {
        }

        explicit Element(IntegerVariableID var, std::pair<IntegerVariableID, Integer> idx, Array array) :
            NDimensionalElement(var, {{idx.first}}, {{idx.second}}, std::move(array), false)
        {
        }
    };

    class Element2D : public NDimensionalElement<IntegerVariableID, 2>
    {
    public:
        explicit Element2D(IntegerVariableID var, IntegerVariableID zero_idx_1, IntegerVariableID zero_idx_2, Array array) :
            NDimensionalElement(var, {{zero_idx_1, zero_idx_2}}, {{0_i, 0_i}}, std::move(array), false)
        {
        }

        explicit Element2D(IntegerVariableID var, std::pair<IntegerVariableID, Integer> idx1, std::pair<IntegerVariableID, Integer> idx2,
            Array array) : NDimensionalElement(var, {{idx1.first, idx2.first}}, {{idx1.second, idx2.second}}, std::move(array), false)
        {
        }
    };

    class ElementConstantArray : public NDimensionalElement<Integer, 1>
    {
    public:
        explicit ElementConstantArray(IntegerVariableID var, IntegerVariableID zero_idx, Array array) :
            NDimensionalElement(var, {{zero_idx}}, {{0_i}}, std::move(array), true)
        {
        }

        explicit ElementConstantArray(IntegerVariableID var, std::pair<IntegerVariableID, Integer> idx, Array array) :
            NDimensionalElement(var, {{idx.first}}, {{idx.second}}, std::move(array), true)
        {
        }
    };

    class Element2DConstantArray : public NDimensionalElement<Integer, 2>
    {
    public:
        explicit Element2DConstantArray(IntegerVariableID var, IntegerVariableID idx1, IntegerVariableID idx2, Array array) :
            NDimensionalElement(var, {{idx1, idx2}}, {{0_i, 0_i}}, std::move(array), true)
        {
        }

        explicit Element2DConstantArray(IntegerVariableID var, std::pair<IntegerVariableID, Integer> idx1, std::pair<IntegerVariableID, Integer> idx2,
            Array array) : NDimensionalElement(var, {{idx1.first, idx2.first}}, {{idx1.second, idx2.second}}, std::move(array), true)
        {
        }
    };
}

#endif
