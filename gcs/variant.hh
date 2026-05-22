#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIANT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_VARIANT_HH

#include <algorithm>
#include <compare>
#include <cstddef>
#include <cstdint>
#include <new>
#include <type_traits>
#include <utility>

namespace gcs
{
    // Empty marker alternative. Behaves the same as std::monostate but lives in gcs::.
    struct monostate
    {
        [[nodiscard]] constexpr auto operator==(const monostate &) const noexcept -> bool = default;
        [[nodiscard]] constexpr auto operator<=>(const monostate &) const noexcept -> std::strong_ordering = default;
    };

    namespace variant_detail
    {
        // Index of T in <Ts...>, or sizeof...(Ts) if not found.
        template <typename T, typename... Ts>
        consteval auto index_of() noexcept -> std::size_t
        {
            constexpr bool matches[] = {std::is_same_v<T, Ts>...};
            for (std::size_t i = 0; i < sizeof...(Ts); ++i)
                if (matches[i]) return i;
            return sizeof...(Ts);
        }

        template <typename T, typename... Ts>
        inline constexpr std::size_t index_of_v = index_of<T, Ts...>();

        template <std::size_t I, typename... Ts>
        struct nth_type;

        template <std::size_t I, typename First, typename... Rest>
        struct nth_type<I, First, Rest...>
        {
            using type = typename nth_type<I - 1, Rest...>::type;
        };

        template <typename First, typename... Rest>
        struct nth_type<0, First, Rest...>
        {
            using type = First;
        };

        template <std::size_t I, typename... Ts>
        using nth_type_t = typename nth_type<I, Ts...>::type;

        // The std::variant "best match" trick. For each alternative T_i, declare an
        // imaginary function FUN_i(T_i) returning integral_constant<size_t, I>. To
        // construct variant<Ts...> from argument U, call FUN(U) and use overload
        // resolution to pick the unique best T_i. If ambiguous or none match, the
        // expression is ill-formed — caught by a requires clause at the call site.
        template <std::size_t I, typename T>
        struct fun_overload
        {
            constexpr auto operator()(T) const noexcept -> std::integral_constant<std::size_t, I>;
        };

        template <typename Sequence, typename... Ts>
        struct fun_overloads_impl;

        template <std::size_t... Is, typename... Ts>
        struct fun_overloads_impl<std::index_sequence<Is...>, Ts...> : fun_overload<Is, Ts>...
        {
            using fun_overload<Is, Ts>::operator()...;
        };

        template <typename... Ts>
        using fun_overloads = fun_overloads_impl<std::index_sequence_for<Ts...>, Ts...>;

        template <typename U, typename... Ts>
        concept variant_convertible_from = requires(U && u) {
            { fun_overloads<Ts...>{}(std::forward<U>(u)) };
        };

        template <typename U, typename... Ts>
            requires variant_convertible_from<U, Ts...>
        inline constexpr std::size_t best_match_v =
            decltype(fun_overloads<Ts...>{}(std::declval<U>()))::value;
    }

    /**
     * \brief Never-valueless tagged-union alternative to std::variant.
     *
     * Requires every alternative to be nothrow move-constructible so we can
     * skip the valueless_by_exception branch on every visit/get/index check.
     * The tag is a uint8_t (so up to 255 alternatives) followed by aligned
     * storage sized for the largest alternative.
     *
     * Drop-in API for the std::variant operations the codebase uses:
     *  - construction from one alternative or default (first alternative)
     *  - copy / move / destructor
     *  - index()
     *  - free `visit`, `get`, `get_if`, `holds_alternative`
     *  - operator== / operator<=> (synthesised across alternatives)
     */
    template <typename... Ts>
    class variant
    {
        static_assert(sizeof...(Ts) > 0, "gcs::variant needs at least one alternative");
        static_assert(sizeof...(Ts) <= 255, "gcs::variant supports up to 255 alternatives (uint8_t tag)");
        static_assert((std::is_nothrow_move_constructible_v<Ts> && ...),
            "gcs::variant alternatives must be nothrow move-constructible (so we can drop the valueless branch)");

    public:
        static constexpr std::size_t alternatives = sizeof...(Ts);

    private:
        template <std::size_t I>
        using nth_t = variant_detail::nth_type_t<I, Ts...>;

        static constexpr std::size_t storage_size = std::max({sizeof(Ts)...});
        static constexpr std::size_t storage_align = std::max({alignof(Ts)...});

        alignas(storage_align) std::byte storage_[storage_size];
        std::uint8_t tag_;

        template <std::size_t I, typename Self>
        [[nodiscard]] static auto storage_as(Self & s) noexcept -> auto *
        {
            using T = std::conditional_t<std::is_const_v<Self>, const nth_t<I>, nth_t<I>>;
            return std::launder(reinterpret_cast<T *>(s.storage_));
        }

        template <std::size_t I, std::size_t N, typename Self, typename Visitor>
        [[gnu::always_inline]] static constexpr auto visit_dispatch(Self & self, Visitor && vis) -> decltype(auto)
        {
            if constexpr (I + 1 < N) {
                if (self.tag_ == I)
                    return std::forward<Visitor>(vis)(*storage_as<I>(self));
                return visit_dispatch<I + 1, N>(self, std::forward<Visitor>(vis));
            }
            else {
                // Must be the last alternative — tag is always a valid index.
                return std::forward<Visitor>(vis)(*storage_as<N - 1>(self));
            }
        }

        template <std::size_t... Is>
        auto destroy_active(std::index_sequence<Is...>) noexcept -> void
        {
            (void)((Is == tag_ ? (storage_as<Is>(*this)->~nth_t<Is>(), true) : false) || ...);
        }

        template <std::size_t... Is>
        auto copy_construct_from(const variant & other, std::index_sequence<Is...>) -> void
        {
            (void)((Is == other.tag_
                       ? (::new (static_cast<void *>(storage_)) nth_t<Is>(*storage_as<Is>(other)), true)
                       : false) ||
                ...);
            tag_ = other.tag_;
        }

        template <std::size_t... Is>
        auto move_construct_from(variant && other, std::index_sequence<Is...>) noexcept -> void
        {
            (void)((Is == other.tag_
                       ? (::new (static_cast<void *>(storage_)) nth_t<Is>(std::move(*storage_as<Is>(other))), true)
                       : false) ||
                ...);
            tag_ = other.tag_;
        }

        using index_seq = std::make_index_sequence<sizeof...(Ts)>;

        // Allow free functions to peek at the storage.
        template <std::size_t I, typename... Us>
        friend constexpr auto get_unchecked(variant<Us...> & v) noexcept -> variant_detail::nth_type_t<I, Us...> &;
        template <std::size_t I, typename... Us>
        friend constexpr auto get_unchecked(const variant<Us...> & v) noexcept -> const variant_detail::nth_type_t<I, Us...> &;

        template <typename Visitor, typename V>
        friend constexpr auto visit(Visitor && vis, V && var) -> decltype(auto);

    public:
        // Default ctor: construct the first alternative.
        constexpr variant() noexcept(std::is_nothrow_default_constructible_v<nth_t<0>>)
            requires std::is_default_constructible_v<nth_t<0>>
        {
            ::new (static_cast<void *>(storage_)) nth_t<0>();
            tag_ = 0;
        }

        // Converting ctor: select the alternative via std::variant's FUN-overload trick.
        template <typename U>
            requires(! std::is_same_v<std::decay_t<U>, variant> &&
                     variant_detail::variant_convertible_from<U, Ts...>)
        constexpr variant(U && u) noexcept(std::is_nothrow_constructible_v<nth_t<variant_detail::best_match_v<U, Ts...>>, U>)
        {
            constexpr std::size_t I = variant_detail::best_match_v<U, Ts...>;
            ::new (static_cast<void *>(storage_)) nth_t<I>(std::forward<U>(u));
            tag_ = static_cast<std::uint8_t>(I);
        }

        variant(const variant & other)
        {
            copy_construct_from(other, index_seq{});
        }

        variant(variant && other) noexcept
        {
            move_construct_from(std::move(other), index_seq{});
        }

        auto operator=(const variant & other) -> variant &
        {
            if (this != &other) {
                destroy_active(index_seq{});
                copy_construct_from(other, index_seq{});
            }
            return *this;
        }

        auto operator=(variant && other) noexcept -> variant &
        {
            if (this != &other) {
                destroy_active(index_seq{});
                move_construct_from(std::move(other), index_seq{});
            }
            return *this;
        }

        // Assign from an alternative (same matching as the converting ctor).
        template <typename U>
            requires(! std::is_same_v<std::decay_t<U>, variant> &&
                     variant_detail::variant_convertible_from<U, Ts...>)
        auto operator=(U && u) noexcept(std::is_nothrow_constructible_v<nth_t<variant_detail::best_match_v<U, Ts...>>, U>) -> variant &
        {
            constexpr std::size_t I = variant_detail::best_match_v<U, Ts...>;
            destroy_active(index_seq{});
            ::new (static_cast<void *>(storage_)) nth_t<I>(std::forward<U>(u));
            tag_ = static_cast<std::uint8_t>(I);
            return *this;
        }

        ~variant()
        {
            destroy_active(index_seq{});
        }

        [[nodiscard]] constexpr auto index() const noexcept -> std::size_t
        {
            return tag_;
        }

    };

    template <std::size_t I, typename... Us>
    [[nodiscard]] constexpr auto get_unchecked(variant<Us...> & v) noexcept -> variant_detail::nth_type_t<I, Us...> &
    {
        return *variant<Us...>::template storage_as<I>(v);
    }

    template <std::size_t I, typename... Us>
    [[nodiscard]] constexpr auto get_unchecked(const variant<Us...> & v) noexcept -> const variant_detail::nth_type_t<I, Us...> &
    {
        return *variant<Us...>::template storage_as<I>(v);
    }

    template <typename Visitor, typename V>
    [[gnu::always_inline]] constexpr auto visit(Visitor && vis, V && var) -> decltype(auto)
    {
        using VarT = std::remove_reference_t<V>;
        return VarT::template visit_dispatch<0, VarT::alternatives>(var, std::forward<Visitor>(vis));
    }

    // Multi-variant visit: dispatch nested through each variant.
    template <typename Visitor, typename V1, typename V2, typename... Vs>
    [[gnu::always_inline]] constexpr auto visit(Visitor && vis, V1 && v1, V2 && v2, Vs &&... vs) -> decltype(auto)
    {
        return visit(
            [&](auto && a1) -> decltype(auto) {
                return visit(
                    [&](auto &&... rest) -> decltype(auto) {
                        return std::forward<Visitor>(vis)(
                            std::forward<decltype(a1)>(a1),
                            std::forward<decltype(rest)>(rest)...);
                    },
                    std::forward<V2>(v2), std::forward<Vs>(vs)...);
            },
            std::forward<V1>(v1));
    }

    template <typename T, typename... Ts>
    [[nodiscard]] constexpr auto holds_alternative(const variant<Ts...> & v) noexcept -> bool
    {
        constexpr std::size_t I = variant_detail::index_of_v<T, Ts...>;
        static_assert(I < sizeof...(Ts), "holds_alternative: T is not one of the variant alternatives");
        return v.index() == I;
    }

    template <typename T, typename... Ts>
    [[nodiscard]] constexpr auto get(variant<Ts...> & v) -> T &
    {
        constexpr std::size_t I = variant_detail::index_of_v<T, Ts...>;
        static_assert(I < sizeof...(Ts), "get: T is not one of the variant alternatives");
        // Caller's responsibility: caller must have checked the index. Matches the pattern
        // in the codebase, where get<T> is always preceded by holds_alternative<T> or visit.
        return get_unchecked<I>(v);
    }

    template <typename T, typename... Ts>
    [[nodiscard]] constexpr auto get(const variant<Ts...> & v) -> const T &
    {
        constexpr std::size_t I = variant_detail::index_of_v<T, Ts...>;
        static_assert(I < sizeof...(Ts), "get: T is not one of the variant alternatives");
        return get_unchecked<I>(v);
    }

    template <std::size_t I, typename... Ts>
    [[nodiscard]] constexpr auto get(variant<Ts...> & v) -> variant_detail::nth_type_t<I, Ts...> &
    {
        static_assert(I < sizeof...(Ts), "get<I>: index out of range");
        return get_unchecked<I>(v);
    }

    template <std::size_t I, typename... Ts>
    [[nodiscard]] constexpr auto get(const variant<Ts...> & v) -> const variant_detail::nth_type_t<I, Ts...> &
    {
        static_assert(I < sizeof...(Ts), "get<I>: index out of range");
        return get_unchecked<I>(v);
    }

    template <typename T, typename... Ts>
    [[nodiscard]] constexpr auto get_if(variant<Ts...> * v) noexcept -> T *
    {
        constexpr std::size_t I = variant_detail::index_of_v<T, Ts...>;
        static_assert(I < sizeof...(Ts), "get_if: T is not one of the variant alternatives");
        if (v && v->index() == I)
            return &get_unchecked<I>(*v);
        return nullptr;
    }

    template <typename T, typename... Ts>
    [[nodiscard]] constexpr auto get_if(const variant<Ts...> * v) noexcept -> const T *
    {
        constexpr std::size_t I = variant_detail::index_of_v<T, Ts...>;
        static_assert(I < sizeof...(Ts), "get_if: T is not one of the variant alternatives");
        if (v && v->index() == I)
            return &get_unchecked<I>(*v);
        return nullptr;
    }

    // Comparison operators are free templates with explicit constraints so they
    // only participate in overload resolution when every alternative supports
    // the relevant comparison. Some empty marker alternatives don't.

    template <typename... Ts>
        requires(std::equality_comparable<Ts> && ...)
    [[nodiscard]] constexpr auto operator==(const variant<Ts...> & a, const variant<Ts...> & b) -> bool
    {
        if (a.index() != b.index()) return false;
        return [&]<std::size_t... Is>(std::index_sequence<Is...>) {
            return ((Is == a.index() ? get_unchecked<Is>(a) == get_unchecked<Is>(b) : false) || ...);
        }(std::make_index_sequence<sizeof...(Ts)>{});
    }

    template <typename... Ts>
        requires(std::three_way_comparable<Ts> && ...)
    [[nodiscard]] constexpr auto operator<=>(const variant<Ts...> & a, const variant<Ts...> & b)
        -> std::common_comparison_category_t<std::compare_three_way_result_t<Ts>...>
    {
        using R = std::common_comparison_category_t<std::compare_three_way_result_t<Ts>...>;
        if (auto c = a.index() <=> b.index(); c != 0)
            return c;
        return [&]<std::size_t... Is>(std::index_sequence<Is...>) -> R {
            R result = R::equivalent;
            (void)((Is == a.index() ? (result = get_unchecked<Is>(a) <=> get_unchecked<Is>(b), true) : false) || ...);
            return result;
        }(std::make_index_sequence<sizeof...(Ts)>{});
    }
}

#endif
