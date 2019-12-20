#include <functional>
#include <tuple>
#include <type_traits>
#include <variant>

#include <hedley/hedley.h>

namespace ubiq::details {
    template <typename Void, typename R, typename F, typename... Ts>
    struct IsInvocableExactImpl : std::false_type { };

    template <typename R, typename F, typename... Ts>
    struct IsInvocableExactImpl<std::void_t<std::invoke_result_t<F, Ts...>>, R, F, Ts...> :
        std::is_same<R, std::invoke_result_t<F, Ts...>> { };

    template <typename R, bool Reachable = true>
    struct SwitchVisitDispatcher {
        template <typename F, typename... Ts>
        static constexpr bool IsInvocableExact = IsInvocableExactImpl<void, typename R::Type, F, Ts...>::value;

        template <typename F, typename... Ts>
        static constexpr bool IsInvocableConvertible = std::is_invocable_r<typename R::Type, F, Ts...>::value;

        template <auto I, typename TVariant>
        HEDLEY_ALWAYS_INLINE static constexpr decltype(auto) Get(TVariant&& Vs) noexcept {
            if (Vs.index() == I) {
                using T = decltype(std::get<I>(std::forward<TVariant>(Vs)));
                return static_cast<T&&>(*std::get_if<I>(&Vs));
            }

            HEDLEY_UNREACHABLE();
        }

        template <typename TCallable, auto... Is, auto... Ns, typename TVariants>
        HEDLEY_ALWAYS_INLINE static constexpr typename R::Type
        Case(TCallable&& Callable, std::index_sequence<Is...>, std::index_sequence<Ns...>, TVariants&& Vs) {
            if constexpr (R::Strict) {
                constexpr bool IsValidInvocation =
                    IsInvocableExact<TCallable, decltype(Get<Is>(std::get<Ns>(std::declval<TVariants>())))...>;

                static_assert(
                    IsValidInvocation,
                    "invocation must be a valid expression of the same type and value category for all "
                    "combinations of alternative types of all variants");
            } else {
                constexpr bool IsValidInvocation =
                    IsInvocableConvertible<TCallable, decltype(Get<Is>(std::get<Ns>(std::declval<TVariants>())))...>;

                static_assert(
                    IsValidInvocation,
                    "invocation must be a valid expression convertible to R for all "
                    "combinations of alternative types of all variants");
            }

            return std::invoke(
                std::forward<TCallable>(Callable),
                Get<Is>(std::get<Ns>(std::forward<TVariants>(Vs)))...);
        }

        template <auto I1, auto I2, typename TCallable, auto... Is, typename TVariants>
        HEDLEY_ALWAYS_INLINE static constexpr typename R::Type
        Switch(TCallable&& Callable, std::index_sequence<Is...>, TVariants&& Vs) {
            if constexpr (I1 == std::tuple_size_v<std::remove_reference_t<TVariants>>) {
                return Case(
                    std::forward<TCallable>(Callable),
                    std::index_sequence<Is...>{},
                    std::make_index_sequence<I1>{},
                    std::forward<TVariants>(Vs));
            } else {
                auto&& Current = std::get<I1>(std::forward<TVariants>(Vs));
                constexpr auto Size = std::variant_size_v<std::remove_reference_t<decltype(Current)>>;
                switch (Current.index()) {
#define CASE_(N)                                                                                                       \
    case I2 + (N):                                                                                                     \
        return SwitchVisitDispatcher<R, (I2 + (N) < Size)>::template Switch<I1 + 1, 0>(                                \
            std::forward<TCallable>(Callable),                                                                         \
            std::index_sequence<Is..., I2 + (N)>{},                                                                    \
            std::forward<TVariants>(Vs))

#define DEFT_(N)                                                                                                       \
    default:                                                                                                           \
        return SwitchVisitDispatcher<R, (I2 + (N) < Size)>::template Switch<I1, I2 + (N)>(                             \
            std::forward<TCallable>(Callable),                                                                         \
            std::index_sequence<Is...>{},                                                                              \
            std::forward<TVariants>(Vs))

                    CASE_(0);
                    CASE_(1);
                    CASE_(2);
                    CASE_(3);
                    CASE_(4);
                    CASE_(5);
                    CASE_(6);
                    CASE_(7);
                    DEFT_(8);
#undef CASE_
#undef DEFT_
                }
            }
        }
    };

    template <typename R>
    struct SwitchVisitDispatcher<R, false> {
        [[noreturn]] static constexpr typename R::Type Switch() noexcept {
            HEDLEY_UNREACHABLE();
        }

        template <auto, auto, typename TCallable, auto... Is, typename TVariants>
        [[noreturn]] static constexpr typename R::Type
        Switch(TCallable&&, std::index_sequence<Is...>, TVariants&&) noexcept {
            HEDLEY_UNREACHABLE();
        }
    };

    template <typename R, bool StrictChecking>
    struct ReturnType {
        using Type = R;
        static constexpr bool Strict = StrictChecking;
    };

    template <typename R, bool StrictChecking, typename TCallable, typename... TVariants>
    HEDLEY_ALWAYS_INLINE constexpr decltype(auto) Visit(TCallable&& Callable, TVariants&&... Vs) {
        if (((Vs.index() != std::variant_npos) && ...)) {
            return SwitchVisitDispatcher<ReturnType<R, StrictChecking>>::template Switch<0, 0>(
                std::forward<TCallable>(Callable),
                std::index_sequence<>{},
                std::forward_as_tuple(std::forward<TVariants>(Vs)...));
        }

        return SwitchVisitDispatcher<ReturnType<R, StrictChecking>, false>::Switch();
    }
}

// ubiq::visit doesn't throw bad_variant_access
// user must ensure that for all variants valueless_by_exception() returns false
namespace ubiq {
    template <typename TCallable, typename... TVariants>
    constexpr decltype(auto) visit(TCallable&& Callable, TVariants&&... Vs) {
        static_assert(sizeof...(TVariants) > 0);

        using R = std::invoke_result_t<TCallable, decltype(std::get<0>(std::declval<TVariants>()))...>;

        return details::Visit<R, true>(std::forward<TCallable>(Callable), std::forward<TVariants>(Vs)...);
    }

    template <typename R, typename TCallable, typename... TVariants>
    constexpr decltype(auto) visit(TCallable&& Callable, TVariants&&... Vs) {
        static_assert(sizeof...(Vs) > 0);

        return details::Visit<R, false>(std::forward<TCallable>(Callable), std::forward<TVariants>(Vs)...);
    }
}