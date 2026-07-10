#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ARRAY_PARAM_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_ARRAY_PARAM_HH

#include <gcs/lifetime.hh>

#include <initializer_list>
#include <memory>
#include <utility>
#include <vector>

namespace gcs
{
    /**
     * \brief A constructor parameter holding array-like data a constraint will
     * read, with caller-chosen ownership.
     *
     * The same handle accepts three forms, so a constraint needs only one
     * parameter rather than a pointer plus a lifetime contract:
     *   - **owned**: a container moved in (`{a, b, c}` or `std::move(vec)`),
     *   - **shared**: a `std::shared_ptr<const C>` reused across constraints
     *     without copying the data,
     *   - **borrowed**: a raw `const C *` to storage the caller keeps alive.
     *
     * Access is pointer-like (`operator*` / `operator->`) and branch-free in
     * every mode. Borrowing aliases an empty `shared_ptr`, which allocates no
     * control block and takes no ownership -- so, exactly as with a raw pointer,
     * the borrowed storage must outlive every use of this handle (and any copy
     * of it, e.g. one captured by a propagator). Copying the handle is cheap (a
     * `shared_ptr` copy), so clone() shares rather than duplicating the data.
     *
     * \ingroup Core
     */
    template <typename C_>
    class ArrayParam
    {
    private:
        std::shared_ptr<const C_> _data;

    public:
        ArrayParam(C_ owned) : _data(std::make_shared<const C_>(std::move(owned)))
        {
        }

        ArrayParam(std::initializer_list<typename C_::value_type> owned) : _data(std::make_shared<const C_>(owned))
        {
        }

        ArrayParam(std::shared_ptr<const C_> shared) : _data(std::move(shared))
        {
        }

        ArrayParam(const C_ * borrowed GCS_LIFETIME_BOUND) : _data(std::shared_ptr<const C_>{}, borrowed)
        {
        }

        [[nodiscard]] auto operator*() const GCS_LIFETIME_BOUND -> const C_ &
        {
            return *_data;
        }

        [[nodiscard]] auto operator->() const GCS_LIFETIME_BOUND -> const C_ *
        {
            return _data.get();
        }
    };

    /**
     * \brief Convenience spelling of the common case, an ArrayParam over a
     * `std::vector<T>` (e.g. `VectorArrayParam<IntegerVariableID>`).
     *
     * \ingroup Core
     */
    template <typename T_>
    using VectorArrayParam = ArrayParam<std::vector<T_>>;
}

#endif
