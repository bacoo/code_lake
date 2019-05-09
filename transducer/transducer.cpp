/*
 * transducer.cpp
 *
 *  Created on: May 9, 2019
 *      Author: bacoo zhao
 *     Compile: g++ -g -Wall -std=c++14 transducer.cpp -o transducer
 *   Reference: http://vitiy.info/cpp14-how-to-implement-transducers/
 *              http://vitiy.info/templates-as-first-class-citizens-in-cpp11/
 *              http://vitiy.info/functional-pipeline-in-c11/
 */

#include <functional>
#include <type_traits>
#include <utility>
#include <vector>
#include <string>
#include <iostream>

template<typename T>
void print_type_trait() {
    std::cout << __PRETTY_FUNCTION__ << std::endl;
}
#define PRINT_TYPE_TRAIT(x) print_type_trait<decltype(x)>()

namespace fn_detail {

template<typename G, typename ... Ts>
struct tr_transducer {
    std::tuple<Ts...> params;

    tr_transducer(Ts ...ts) :
            params(std::make_tuple(ts...)) {
    }

    template<typename RF>
    auto operator()(RF&& step) const {
        return this->make(std::forward<RF>(step),
                std::make_index_sequence<sizeof...(Ts)>());
    }

    template<typename RF, std::size_t...indexes_t>
    auto make(RF step, std::index_sequence<indexes_t...>) const
    -> typename G::template apply<RF, Ts...>
    {
        return {std::forward<RF>(step), std::get<indexes_t>(params)...};
    }
};

template<typename ... T>
void noop(T ... ts) {
}

struct tr_map_gen {
    template<typename ReducingFnT, typename MappingT>
    struct apply {
        ReducingFnT step;
        MappingT mapping;

        template<typename StateT, typename ...InputTs>
        bool operator()(StateT& out, InputTs&& ...ins) {
            return step(out, mapping(std::forward<decltype(ins)>(ins)...));
        }
    };
};

struct tr_filter_gen {
    template<typename ReducingFnT, typename FilterT>
    struct apply {
        ReducingFnT step;
        FilterT pred;

        template<typename StateT, typename ...InputTs>
        bool operator()(StateT& out, InputTs&& ...ins) {
            if (pred(std::forward<decltype(ins)>(ins)...))
                return step(out, std::forward<decltype(ins)>(ins)...);
            else
                return true;
        }
    };
};

struct tr_enumerate_gen {
    template<typename ReducingFnT, typename N>
    struct apply {
        ReducingFnT step;
        int n;

        template<typename StateT, typename ...InputTs>
        bool operator()(StateT& out, InputTs&& ...ins) {
            return step(out, n++, std::forward<decltype(ins)>(ins)...);
        }
    };
};

struct tr_limit_gen {
    template<typename ReducingFnT, typename N1, typename N2>
    struct apply {
        ReducingFnT step;
        int n;
        int limit;

        template<typename StateT, typename ...InputTs>
        bool operator()(StateT& out, InputTs&& ...ins) {
            return (n++ > limit) ?
                    false : step(out, std::forward<decltype(ins)>(ins)...);
        }
    };
};

struct tr_each_gen {
    template<typename ReducingFnT, typename EachFnT>
    struct apply {
        ReducingFnT step;
        EachFnT each;

        template<typename StateT, typename ...InputTs>
        bool operator()(StateT& out, InputTs&& ...ins) {
            each(std::forward<decltype(ins)>(ins)...);
            return true;
        }
    };
};

} // end of namespace fn_detail

template<typename T>
auto tr_map(T f) {
    return fn_detail::tr_transducer<fn_detail::tr_map_gen, T>(f);
}

template<typename T>
auto tr_filter(T pred) {
    return fn_detail::tr_transducer<fn_detail::tr_filter_gen, T>(pred);
}

auto tr_enumerate(int n = 0) {
    return fn_detail::tr_transducer<fn_detail::tr_enumerate_gen, int>(n);
}

auto tr_limit(int limit) {
    return fn_detail::tr_transducer<fn_detail::tr_limit_gen, int, int>(1, limit);
}

template<typename T>
auto tr_each(T each) {
    return fn_detail::tr_transducer<fn_detail::tr_each_gen, T>(each);
}

/// The inversed chain of functors ... is actually just a tuple of functors
template<typename ... FNs>
class fn_chain_reversed {
private:
    const std::tuple<FNs...> functions;

    template<std::size_t I, typename Arg>
    inline typename std::enable_if<I == sizeof...(FNs) - 1, decltype(std::get<I>(functions)(std::declval<Arg>())) >::type
    call(Arg arg) const
    {
        return std::get<I>(functions)(std::forward<Arg>(arg));
    }

    template <std::size_t N, std::size_t I, typename Arg>
    struct final_type : final_type<N-1, I+1, decltype(std::get<I>(functions)(std::declval<Arg>())) > {};

    template <std::size_t I, typename Arg>
    struct final_type<0, I, Arg> {
        using type = decltype(std::get<I>(functions)(std::declval<Arg>()));
    };

    template <std::size_t I, typename Arg>
    inline typename std::enable_if<I < sizeof...(FNs) - 1, typename final_type<sizeof...(FNs) - 1 - I, I, Arg>::type >::type
    call(Arg arg) const
    {
        return this->call<I+1>(std::get<I>(functions)(std::forward<Arg>(arg)));
    }

    static const bool isFunctionalChain = true;

public:
    fn_chain_reversed() : functions(std::tuple<>()) {}
    fn_chain_reversed(std::tuple<FNs...> functions) : functions(functions) {}

    // add function into chain (inversed order)
    template< typename F >
    inline auto add(const F& f) const -> fn_chain_reversed<F,FNs...>
    {
        return fn_chain_reversed<F,FNs...>(std::tuple_cat(std::make_tuple(f), functions));
    }

    // call whole functional chain
    template <typename Arg>
    inline auto operator()(Arg arg) const -> decltype(this->call<0,Arg>(arg))
    {
        return call<0>(std::forward<Arg>(arg));
    }

};

template<typename ... FNs, typename F>
inline auto operator|(fn_chain_reversed<FNs...> && transducer,
        F&& rf) -> decltype(transducer.add(rf)) {
    return transducer.add(std::forward<F>(rf));
}

template<typename T, typename ... FNs>
struct fn_isNotFunctionalChain {
    static const bool value = true;
};

template<>
struct fn_isNotFunctionalChain<fn_chain_reversed<> > {
    static const bool value = false;
};

template<typename T, class F, typename = std::enable_if_t<
        fn_isNotFunctionalChain<F>::value> >
auto operator|(const F& f, T&& param) -> decltype(f(param)) {
    return f(std::forward<T>(param));
}

#define tr fn_chain_reversed<>()

template<std::size_t Index, std::size_t Max>
struct tuple_all_neq_t {
    template<typename Tuple1T, typename Tuple2T>
    bool operator()(Tuple1T&& t1, Tuple2T&& t2) {
        return std::get<Index>(std::forward<Tuple1T>(t1))
                != std::get<Index>(std::forward<Tuple2T>(t2))
                && tuple_all_neq_t<Index + 1, Max> { }(
                        std::forward<Tuple1T>(t1), std::forward<Tuple2T>(t2));
    }
};

template<std::size_t Max>
struct tuple_all_neq_t<Max, Max> {
    template<typename Tuple1T, typename Tuple2T>
    bool operator()(Tuple1T&&, Tuple2T&&) {
        return true;
    }
};

template<typename Tuple1T, typename Tuple2T>
bool tuple_all_neq(Tuple1T&& t1, Tuple2T&& t2) {
    constexpr auto size1 = std::tuple_size<std::decay_t<Tuple1T> >::value;
    constexpr auto size2 = std::tuple_size<std::decay_t<Tuple2T> >::value;

    using impl_t = tuple_all_neq_t<0u, (size1 > size2 ? size2 : size1)>;

    return impl_t { }(std::forward<Tuple1T>(t1), std::forward<Tuple2T>(t2));
}

template<typename RF, typename A, std::size_t ...Indices, typename ...Ranges>
auto fn_accum_impl(std::index_sequence<Indices...>, RF&& step, A& out,
        Ranges ... ranges) {
    auto firsts = std::make_tuple(std::begin(ranges)...);
    auto lasts = std::make_tuple(std::end(ranges)...);

    bool ok = true;
    // just loop once
    while (tuple_all_neq(firsts, lasts) && (ok)) {
        ok = step(out, std::forward< decltype(*std::begin(ranges)) >(*std::get<Indices>(firsts))...);
        fn_detail::noop(++std::get<Indices>(firsts)...);
    }
}

template<typename T, typename RF, typename C, typename ... Ins>
auto fn_tr_transduce(C init, T&& transducer, RF&& reducingFunction, Ins ... ins) {
    C out = init;
    fn_accum_impl(std::make_index_sequence<sizeof...(Ins)> {},
            transducer(reducingFunction),
            out,
            (std::forward<Ins>(ins))...);
    return std::move(out);
}

template<typename RF, typename C, typename ... Ins>
auto fn_into_vector(RF step, C input, Ins ... ins) {
    return fn_tr_transduce(
            std::vector<std::decay_t<decltype(*std::begin(input))>>(), step,
            [] (auto& out, auto input) {
                out.push_back(input);
                return true;
            }, std::forward<C>(input), (std::forward<Ins>(ins))...);
}

template<typename T, typename C, typename ... Ins>
auto fn_tr_reduce(C&& init, T&& step, Ins ... ins) {
    C&& out = std::forward<C>(init);
    fn_accum_impl(std::make_index_sequence<sizeof...(Ins)> {},
            std::forward<T>(step),
            out,
            (std::forward<Ins>(ins))...);
    return std::move(out);
}

template<typename T, typename ... Ins>
void fn_tr_end(T&& step, Ins ... ins) {
    auto step_wrap = step([](){});
    int out = 0;
    fn_accum_impl(std::make_index_sequence<sizeof...(Ins)> {},
            std::forward<decltype(step_wrap)>(step_wrap),
            out,
            (std::forward<Ins>(ins))...);
}

void my_func(int n, int x) {
    std::cout << n << ":" << x << std::endl;
}
int main(int argc, char* argv[]) {
    std::vector<int> input { 1, 2, 3, 4, 5, 6 };

    {
        auto piping = tr | tr_map([](int x){return 2*x;}) | tr_filter([](int x){return x > 3 && x < 10;}) | tr_limit(2);
        auto transducer = piping([](std::vector<int>& out, int x) {
            out.push_back(x);
            return true;
        });
        //[with T =
        //    fn_chain_reversed<
        //        fn_detail::tr_transducer<fn_detail::tr_limit_gen, int, int>,
        //        fn_detail::tr_transducer<fn_detail::tr_filter_gen, main(int, char**)::<lambda(int)> >,
        //        fn_detail::tr_transducer<fn_detail::tr_map_gen, main(int, char**)::<lambda(int)> >
        //    >
        //]
        PRINT_TYPE_TRAIT(piping);
        //[with T =
        //    fn_detail::tr_map_gen::apply<
        //        fn_detail::tr_filter_gen::apply<
        //            fn_detail::tr_limit_gen::apply<
        //                main(int, char**)::<lambda(std::vector<int>&, int)>,
        //                int,
        //                int
        //            >,
        //            main(int, char**)::<lambda(int)>
        //        >,
        //        main(int, char**)::<lambda(int)>
        //    >
        //]
        PRINT_TYPE_TRAIT(transducer);
        auto result = fn_tr_reduce(std::vector<int>(), transducer, input);
        // output:
        // 4
        // 6
        for (auto x : result) {
            std::cout << x << std::endl;
        }
    }

    std::cout << "============" << std::endl;

    {
        auto result = fn_into_vector(tr |
            tr_map([](int x){
                std::vector<int> v;
                for (int i = 1; i <= x; ++i) {
                    v.push_back(i);
                }
                return v;
            }) |
            tr_map([](std::vector<int> v) {
                int sum = 0;
                for (auto x : v) {
                    sum += x;
                }
                return sum;
            }) |
            tr_filter([](int x){
                return x > 4;
            }), input);
        // output:
        // 6
        // 10
        // 15
        // 21
        for (auto x : result) {
            std::cout << x << std::endl;
        }
    }

    std::cout << "============" << std::endl;

    {
        std::vector<int> input2 { 4, 5, 6, 7 };
        auto result = fn_into_vector(tr | tr_map([](int x, int y){ return x + y; }) | tr_filter([](int x){ return x > 5; }), input, input2);
        // output:
        // 7
        // 9
        // 11
        for (auto x : result) {
            std::cout << x << std::endl;
        }
    }

    std::cout << "============" << std::endl;

    {
        auto enumerateStrings = (tr | tr_enumerate(1) | tr_limit(3) | tr_map([](int idx, std::string s) {
                char buf[1024];
                sprintf(buf, "elements[%d]=%s", idx, s.data());
                return std::string(buf);
            }))([](std::vector<std::string>& out, std::string s) {
                out.push_back(s);
                return true;
            });
        auto result = fn_tr_reduce(std::vector<std::string>(), enumerateStrings, std::vector<std::string>{"a","b","c", "d"});
        // output:
        // elements[1]=a
        // elements[2]=b
        // elements[3]=c
        for (auto x : result) {
            std::cout << x << std::endl;
        }
    }

    std::cout << "============" << std::endl;

    {
        // output:
        // elements[1]=4
        // elements[3]=6
        // elements[5]=8
        fn_tr_end(tr | tr_enumerate() | tr_filter([](int idx, int n){return idx % 2;}) |
                tr_limit(3) | tr_each([](int idx, int n){ std::cout << "elements[" << idx << "]=" << n << std::endl; }),
            std::vector<int>{3, 4, 5, 6, 7, 8, 9});
    }

    return 0;
}
