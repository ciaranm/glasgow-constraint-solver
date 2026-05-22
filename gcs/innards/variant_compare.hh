#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_VARIANT_COMPARE_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_VARIANT_COMPARE_HH

#include <boost/variant2/variant.hpp>

#include <compare>

// Pilot scaffolding: boost::variant2::variant provides operator< / operator==
// but not operator<=> (unlike std::variant). Several gcs types use
// `operator<=> = default` on structs whose members are variants; without a
// three-way operator on the variant, the default is implicitly deleted.
//
// Inject a synthesised three-way operator into namespace boost::variant2 so
// it is found via ADL by the defaulted operators downstream.
namespace boost::variant2
{
    template <typename... Ts>
    [[nodiscard]] constexpr auto operator<=>(const variant<Ts...> & a, const variant<Ts...> & b) -> std::strong_ordering
    {
        if (a == b)
            return std::strong_ordering::equal;
        return (a < b) ? std::strong_ordering::less : std::strong_ordering::greater;
    }
}

#endif
