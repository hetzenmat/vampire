
#include "Debug/Tracer.hpp"
#include "Lib/STLAllocator.hpp"
#include "Lib/Optional.hpp"
#include <map>
#include <vector>
#include <stack>
#include "Ordering.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

#define TODO throw "TODO";


using namespace Lib;

namespace Kernel {

template<Theory::Interpretation inter> LitEvalResult 
  evaluateLit(Literal* lit);


template<Theory::Interpretation inter>
struct FunctionEvaluator {
  template<class PolynomialNormalizerConfig>
  static TermEvalResult evaluate(Term* orig, TermEvalResult* evaluatedArgs);
};

#define IMPL_EVALUATE_FUN(interpretation, ...)\
  template<>  \
  struct FunctionEvaluator<interpretation> { \
    template<class Config> \
    static TermEvalResult evaluate(Term* orig, TermEvalResult* evaluatedArgs) \
    { \
      CALL("FunctionEvaluator<" #interpretation ">::evaluate(Term*,TermEvalResult*)"); \
      __VA_ARGS__ \
    } \
  };

template<class CommutativeMonoid>
TermEvalResult evaluateCommutativeMonoid(Term* orig, TermEvalResult* evaluatedArgs) ;

template<class ConstantType, class EvalIneq> 
LitEvalResult evaluateInequality(Literal* lit, bool strict, EvalIneq evalIneq) ;

template<class ConstantType, class EvalGround>
LitEvalResult tryEvalConstant1(Literal* lit, EvalGround fun);

template<class ConstantType, class EvalGround>
LitEvalResult tryEvalConstant2(Literal* lit, EvalGround fun);

template<class ConstantType, class EvalGround>
TermEvalResult tryEvalConstant1(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun);

template<class number> 
TermEvalResult evaluateMul(TermEvalResult&& lhs, TermEvalResult&& rhs);

template<class ConstantType, class EvalGround>
TermEvalResult tryEvalConstant2(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun);

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Data structures
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class K, class V, class Compare = std::less<K>> using map  = std::map<K, V, Compare, STLAllocator<std::pair<const K, V > > >;

template<class t> using vector  = std::vector<t, STLAllocator<t>>;
template<class t> using stack  = std::stack<t, STLAllocator<t>>;

/** Merges two map-like vectors into a new map-like vector. 
 * A vector is map-like if has key-value pairs as entry, is sorted by keys and each key is unique within the vector.
 *
 * If there is a key present in both lhs and rhs, the corresponding the two corresponding values will be combined 
 * with the closure @b add. After that the result of combining is then used as argument for @b filter() and will 
 * be discarded if filter returns false.
 */
template<class A, class B, class Add, class Filter>
vector<tuple<A, B>> merge_sort_with(const vector<tuple<A, B>>& lhs, const vector<tuple<A, B>>& rhs, Add add, Filter filter) {
    CALL("merge_sort_with()")

    vector<tuple<A,B>> out;
    /* is needed at least */
    out.reserve(max(lhs.size(), rhs.size()));
    auto l = lhs.begin();
    auto r = rhs.begin();
    auto insert = [&](const A& key, B value) {
      ASS(filter(value));
      out.emplace_back(make_tuple(A(key), value));
    };
    auto fst = [](const tuple<A,B>& x) { return get<0>(x); };
    auto snd = [](const tuple<A,B>& x) { return get<1>(x); };
    while (l != lhs.end() && r != rhs.end() ) {
      if (fst(*l) == fst(*r)) {
        //add up
        auto sum = add(snd(*l), snd(*r));
        if (filter(sum))
          insert(fst(*l), sum);
        l++;
        r++;
      } else if (fst(*l)< fst(*r)) {
        // insert l
        insert(fst(*l), snd(*l));
        l++;
      } else {
        // insert r
        insert(fst(*r), snd(*r));
        r++;
      }
    }
    while (l != lhs.end()) {
      insert(fst(*l), snd(*l));
      l++;
    }
    while (r != rhs.end()) {
      insert(fst(*r), snd(*r));
      r++;
    }
    ASS(l == lhs.end() && r == rhs.end());
    return std::move(out);
}


template<class number>
class Monom { 
public:
  using Coeff = typename number::ConstantType;
  class MonomInner;
  struct Hasher;
  Monom& operator=(const Monom&) = default;
  Monom(Monom&&) = default;

private:
  MonomInner* _inner;
  static Map<MonomInner, MonomInner*, Hasher> monoms;

public:

  bool isOne() const {return _inner->isOne();}

  template<class Config>
  TermList toTerm() {return _inner->template toTerm<Config>();}

  friend bool operator<(const Monom& lhs, const Monom& rhs) { return lhs._inner < rhs._inner; }

  friend bool operator==(const Monom& lhs, const Monom& rhs) {return lhs._inner == rhs._inner;}
  size_t hash() const { return std::hash<size_t>{}((size_t) _inner); }

  friend ostream& operator<<(ostream& out, const Monom& m) {return out << *m._inner;}

  Monom(const Monom& other) : _inner(other._inner) {}
  Monom& operator=(Monom&& other) = default;  
  Monom(MonomInner* inner) : _inner(inner) {}
  Monom() : _inner(MonomInner::create(MonomInner())) {}

  Monom(TermList t) : _inner(MonomInner::create(MonomInner(t))) {}
  Monom(TermList factor1, TermList factor2) : _inner(MonomInner::create(MonomInner(factor1, factor2))) { }


  static Monom monom_mul(const Monom& lhs, const Monom& rhs) {
    return Monom(MonomInner::monom_mul(*lhs._inner, *rhs._inner));
  }

  // Monom& operator=(Monom&&) = default;
  class MonomInner {
    vector<tuple<TermList, int>> _factors;
    Optional<TermList> _toTerm;
    friend class Monom;

    // empty monom == 1
    static MonomInner* create(MonomInner&& self) {
      CALL("MonomInner::create(MonomInner&&)")
      return monoms.getOrInit(MonomInner(self),
          [=](MonomInner** toInit) {*toInit = new MonomInner(std::move(self));});
    }

  public:
    MonomInner() : _factors(decltype(_factors)()) { }
    private:

    MonomInner(decltype(_factors) factors) : _factors(factors) { }

    MonomInner(TermList t) : _factors { make_tuple(t, 1)}  { }
    MonomInner(TermList t1, TermList t2) 
      : _factors(t1 == t2 ? decltype(_factors) ({ make_tuple(t1, 2)}) : 
                 t1 <  t2 ? decltype(_factors) ({ make_tuple(t1,1), make_tuple(t2,1)}) :
                            decltype(_factors) ({ make_tuple(t2,1), make_tuple(t1,1)}) 
                            )  { }

    public:

      USE_ALLOCATOR(MonomInner)
      CLASS_NAME(MonomInner)
      using monom_pair = typename decltype(_factors)::value_type;

    static TermList getTerm(const typename decltype(_factors)::value_type& pair) {
      return std::get<0>(pair);
    }

    static int getCount(const typename decltype(_factors)::value_type& pair) {
      return std::get<1>(pair);
    }

    bool isOne() const  {
      return _factors.begin() == _factors.end();
    }

    static TermList pairToTerm(const monom_pair& pair) {
      auto cnt = getCount(pair);
      ASS_REP(cnt > 0, cnt)

      auto trm = getTerm(pair);
      auto out = trm;
      for (auto i = 1; i < cnt; i++) {
        out = number::mul(trm, out);
      }
      return out;
    }

    template<class Config>
    TermList toTerm() {
      CALL("MonomInner::toTerm()")
      return _toTerm.unwrapOrInit([&]() {

        if (_factors.size() == 0) {
          return number::one();
        } else {

          vector<TermList> factors;
          auto sz = 0;
          for(auto& f : _factors) {
            sz += getCount(f);
          }
          factors.reserve(sz);

          for (auto f : _factors) {
            for (auto i = 0; i < getCount(f); i++) {
              factors.push_back(getTerm(f));
            }
          }

          sort(begin(factors), end(factors), typename Config::Ordering{});

          auto iter = factors.rbegin();

          auto out = *iter;
          iter++;
          for(; iter != factors.rend(); iter++)  {
            out = number::mul(*iter, out); 
          }
          return out;
        }
      });
    }

    friend std::ostream& operator<<(std::ostream& out, const MonomInner& self) {
      if (self._factors.size() == 0) {
        return out << "1";
      } else {
        auto iter  = self._factors.begin();
        out << getTerm(*iter) << "^" << getCount(*iter);
        iter++;
        for (; iter != self._factors.end(); iter++) {
          out << " * " << getTerm(*iter) << "^" << getCount(*iter);
        }
        return out;
      }
    }

    friend bool operator<(const MonomInner& l, const MonomInner& r) {
      if (l._factors.size() < r._factors.size()) {
        return true;
      } else if (l._factors.size() > r._factors.size()) {
        return false;
      } else {
        return  l._factors < r._factors;
      }
    }

    friend bool operator==(const MonomInner& l, const MonomInner& r) {
      return l._factors == r._factors;
    }

    public:

    MonomInner& operator=(MonomInner&&) = default;
    MonomInner(MonomInner&&) = default;

    static MonomInner* monom_mul(const MonomInner& lhs, const MonomInner& rhs) {
      return MonomInner::create(MonomInner(merge_sort_with(lhs._factors,rhs._factors,
             [](int l, int r) { return l + r; },
             [](int l) { return l != 0; })));
    }

    explicit MonomInner(const MonomInner&) = default;
    explicit MonomInner(MonomInner&) = default;
  };
  struct Hasher {

    static unsigned hash(Monom::MonomInner const& x) noexcept {
      unsigned out = 0;
      for (auto f : x._factors) {
        out ^= TermListHash::hash(std::get<0>(f));
        out ^= std::hash<int>{}(std::get<1>(f));
        out <<= 1;
      }
      return out;
    }

    static bool equals(Monom::MonomInner const& lhs, Monom::MonomInner const& rhs) noexcept {
      return lhs == rhs;
    }
  };
};


/**
 * A polynomial of a specific interpreted number sort. The type parameter is expected to be an instance of num_traits<...>, 
 * defined in num_traits.hpp.
 */
template<class number>
class Polynom {
public:
  using Coeff = typename number::ConstantType;
  using Monom = Monom<number>;

private:
  class ComplexPolynom;

  struct Hasher;

  using Inner = Coproduct<ComplexPolynom*, Coeff>;
  Inner _inner;
  static Map<ComplexPolynom, ComplexPolynom*, Hasher> polynoms;

public:

  friend ostream& operator<<(ostream& out, const Polynom& self) { 
    self._inner.template match<void>(
          [&](ComplexPolynom* poly) { out << *poly; }
        , [&](Coeff self          ) { out << self; }
        );
    return out;
  }
  template<class Config>
  static TermList toTerm(Polynom& self) { 
    return self._inner.template match<TermList>(
          [](ComplexPolynom* self) { return ComplexPolynom::template toTerm<Config>(*self); }
        , [](Coeff self          ) { return TermList(theory->representConstant(self)); }
        );
  }
public:

  template<class Config>
  inline static Polynom poly_mul(const Polynom& lhs, const Polynom& rhs) {
    return lhs._inner.template match<Polynom>(
          [&](ComplexPolynom* const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](ComplexPolynom* const& rhs) { 
                    if(Config::usePolyMul) {
                      return Polynom(ComplexPolynom::poly_mul(*lhs, *rhs)); 
                    } else {
                      auto l = ComplexPolynom::template toTerm<Config>(*lhs);
                      auto r = ComplexPolynom::template toTerm<Config>(*rhs);
                      return Polynom(ComplexPolynom::create(ComplexPolynom(Monom(l,r))));
                    }
                  }
                , [&](Coeff           const& rhs) { return ComplexPolynom::coeff_poly_mul(rhs, lhs); }
                );
          }
        , [&](Coeff const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](ComplexPolynom* const& rhs) { return ComplexPolynom::coeff_poly_mul(lhs, rhs); }
                , [&](Coeff           const& rhs) { return Polynom(lhs * rhs); }
                );
        });
  }

  inline static Polynom poly_add(const Polynom& lhs, const Polynom& rhs) {
    return lhs._inner.template match<Polynom>(
          [&](ComplexPolynom* const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](ComplexPolynom* const& rhs) { return ComplexPolynom::poly_add(*lhs, *rhs); }
                , [&](Coeff           const& rhs) { return Polynom(ComplexPolynom::add(rhs, lhs)); }
                );
          }
        , [&](Coeff const& lhs) { 
            return rhs._inner.template match<Polynom>(
                  [&](ComplexPolynom* const& rhs) { return Polynom(ComplexPolynom::add(lhs, rhs)); }
                , [&](Coeff           const& rhs) { return Polynom(lhs + rhs); }
                );
        });
  }

  Polynom(Coeff coeff, TermList t) : _inner(Inner::template variant<0>(ComplexPolynom::create(ComplexPolynom(coeff, t)))) {}
  explicit Polynom(Coeff constant)          : _inner(Inner::template variant<1>(constant)) {}
  explicit Polynom(ComplexPolynom* inner)   : _inner(Inner::template variant<0>(inner)) {} 

private:

  class ComplexPolynom {
  public:
    USE_ALLOCATOR(ComplexPolynom)
    CLASS_NAME(ComplexPolynom)

  private:
    vector<tuple<Monom, Coeff>> _coeffs;
    Optional<TermList> _toTerm;
    using poly_pair = typename decltype(_coeffs)::value_type;

  public:

    ComplexPolynom(Coeff coeff, Monom&& t) : _coeffs(decltype(_coeffs)())  { 
      _coeffs.emplace_back(poly_pair(std::move(t), coeff));
    }

    ComplexPolynom(Monom&& t) : _coeffs(decltype(_coeffs)())  { 
      _coeffs.emplace_back(poly_pair(std::move(t), Coeff(1)));
    }

    ComplexPolynom(Coeff coeff, TermList t) : ComplexPolynom(coeff, Monom(t))  { 
      // _coeffs.emplace_back(poly_pair(Monom(t), coeff));
    }

    ComplexPolynom(Coeff constant) : _coeffs(decltype(_coeffs)())  { 
      CALL("ComplexPolynom::ComplexPolynom(Coeff)")
      if (constant != number::zeroC)
        _coeffs.emplace_back(poly_pair(Monom(), constant));
    }

    ComplexPolynom(decltype(_coeffs) coeffs) : _coeffs(coeffs) { }

    ComplexPolynom() : _coeffs(decltype(_coeffs)()) {
    }

    ComplexPolynom(ComplexPolynom&& other) = default;
    explicit ComplexPolynom(const ComplexPolynom&) = default;

    ComplexPolynom& operator=(ComplexPolynom&& other) = default;


    static ComplexPolynom* create(ComplexPolynom&& self) {
      return polynoms.getOrInit(ComplexPolynom(self), 
          [=](ComplexPolynom** toInit) { *toInit = new ComplexPolynom(std::move(self)); });
    }

    friend bool operator==(const ComplexPolynom& lhs, const ComplexPolynom& rhs) {
      return lhs._coeffs == rhs._coeffs;
    }

    static Monom& getMonom(poly_pair& pair) {
      return std::get<0>(pair);
    }

    static const Monom& getMonom(const poly_pair& pair) {
      return std::get<0>(pair);
    }

    static const Coeff& getCoeff(const poly_pair& pair) {
      return std::get<1>(pair);
    }

    static Coeff& getCoeffMut(poly_pair& pair) {
      return std::get<1>(pair);
    }

    static Polynom poly_add(const ComplexPolynom& lhs, const ComplexPolynom& rhs) {
      CALL("ComplexPolynom::poly_add")
      ASS(!lhs._coeffs.empty())
      ASS(!rhs._coeffs.empty())
      auto newCoeffs = merge_sort_with(lhs._coeffs, rhs._coeffs, 
              [](Coeff l, Coeff r){ return l + r; },
              [](Coeff x){ return x != number::zeroC; }
            );
      // if (newCoeffs.empty())  {
      //   return Polynom(Coeff(0));
      // } else {
        return Polynom(ComplexPolynom::create(ComplexPolynom(std::move(newCoeffs))));
      // }
    }

    inline static ComplexPolynom* add(Coeff coeff, ComplexPolynom* old_) {
      CALL("ComplexPolynom::add(Coeff coeff, const ComplexPolynom& old) ")
      const auto& oldPoly = *old_;

      ASS(!oldPoly._coeffs.empty())
      if (coeff == Coeff(0)) {
        return old_;
      } 

      ComplexPolynom newPoly;
      if (getMonom(oldPoly._coeffs[0]).isOne()) {
        ASS(oldPoly._coeffs.begin() != oldPoly._coeffs.end())

        auto newVal = getCoeff(oldPoly._coeffs[0]) + coeff;
        if (newVal == Coeff(0)) {
          /* skipping zero constant value */
          newPoly._coeffs.reserve(oldPoly._coeffs.size() - 1);
          
          auto iter = oldPoly._coeffs.begin();
          iter++;
          for (; iter !=  oldPoly._coeffs.end(); iter++) {
            newPoly._coeffs.emplace_back(poly_pair(*iter));
          }
        } else {
          /* skipping zero constant value */
          newPoly._coeffs = oldPoly._coeffs;
          getCoeffMut(newPoly._coeffs[0]) = newVal;
        }
      } else {
        newPoly._coeffs.reserve(oldPoly._coeffs.size() + 1);
        newPoly._coeffs.push_back(poly_pair(Monom(), coeff));
        for (auto& f : oldPoly._coeffs) {
          // newPoly.push_back(poly_pair(Monom(getMonom(p), getMonom())))
          newPoly._coeffs.push_back(poly_pair(f));
        }
      }

      // DBG("in : ", oldPoly, "\t+\t", coeff)
      // DBG("out: ", newPoly)

      return ComplexPolynom::create(std::move(newPoly));
    }

    static Polynom coeff_poly_mul(Coeff coeff, ComplexPolynom* old_) {
      CALL("ComplexPolynom::coeff_poly_mul(Coeff coeff, ComplexPolynom* old) ")
      const auto& old = *old_;

      if (coeff == Coeff(0)) {
        return Polynom(Coeff(0));

      } else if (coeff == Coeff(1)) {
        return Polynom(old_);

      } else {
        ComplexPolynom newPoly;

        newPoly._coeffs.reserve(old._coeffs.size());
        for (auto& p : old._coeffs) {
          newPoly._coeffs.push_back(poly_pair(Monom(getMonom(p)), coeff * getCoeff(p)));
        }

        return Polynom(ComplexPolynom::create(std::move(newPoly)));
      }
    }

    static ComplexPolynom* poly_mul(const ComplexPolynom& lhs, const ComplexPolynom& rhs) {

      CALL("ComplexPolynom::poly_mul")
      DEBUG("lhs: ", lhs)
      DEBUG("rhs: ", rhs)

      map<Monom, Coeff> prods;

      for (auto& l : lhs._coeffs) {
        for (auto& r : rhs._coeffs) {
          Monom monom = Monom::monom_mul( getMonom(l), getMonom(r));
          auto coeff = getCoeff(l) * getCoeff(r);
          auto res = prods.emplace(make_pair(move(monom), coeff));
          if (!res.second) {
            auto& iter = res.first;
            ASS(iter != prods.end());
            iter->second = iter->second + coeff;
          }
        }
      }
      ComplexPolynom out;
      out._coeffs.reserve(prods.size());
      for (auto iter = prods.begin(); iter != prods.end(); iter++) {
        auto coeff = iter->second;
        if (coeff != number::zeroC) {
          out._coeffs.emplace_back(poly_pair(iter->first, coeff)); 
        }
      }
      DEBUG("out: ", out)
      out.integrity();
      return ComplexPolynom::create(std::move(out));
    }
    void integrity() const {
#if VDEBUG
      if (_coeffs.size() > 0) {
        auto iter = this->_coeffs.begin();
        auto last = iter++;
        while (iter != _coeffs.end()) {
          ASS_REP(getMonom(*last) < getMonom(*iter), *this);
          last = iter++;
        }
      }
#endif
    }

    template<class Config>
    static TermList toTerm(ComplexPolynom& self) {
      CALL("ComplexPolynom::toTerm() const")
      return self._toTerm.unwrapOrInit([&]() {
        // self.integrity();
        
        auto trm = [](poly_pair& x) -> TermList { 

          if (getMonom(x).isOne()) {  
            /* the pair is a plain number */
            return TermList( theory->representConstant(getCoeff(x)) );

          } else if (getCoeff(x)== number::constant(1)) {
            /* the pair is an uninterpreted term */
            return getMonom(x).template toTerm<Config>();

          } else if (getCoeff(x)== number::constant(-1)) {
            return TermList(number::minus(getMonom(x).template toTerm<Config>()));

          } else {
            return TermList(number::mul(TermList( theory->representConstant(getCoeff(x)) ), getMonom(x).template toTerm<Config>())); 
          }
        };

        vector<TermList> coeffs(self._coeffs.size());
        transform(begin(self._coeffs),end(self._coeffs), begin(coeffs), trm);

        sort(begin(coeffs), end(coeffs), typename Config::Ordering{});

        auto iter = coeffs.rbegin(); 
        if (iter == coeffs.rend()) {
          return TermList(number::zero());
        } else {
          auto out = *iter;
          iter++;
          for (; iter != coeffs.rend(); iter++) {
            out = number::add(*iter, out);
          }
          return out;
        }
      });
    }

    friend std::ostream& operator<<(std::ostream& out, const ComplexPolynom& self) {
      auto iter = self._coeffs.begin();
      if ( iter == self._coeffs.end() ) {
        out << "0";
      } else {
        out << getMonom(*iter)<< " * " << getCoeff(*iter);
        iter++;
        for (; iter != self._coeffs.end(); iter++) {
          out << " + " << getMonom(*iter)<< " * " << getCoeff(*iter);
        }
      }
      return out;
    }

    friend struct Hasher;
  };
  struct Hasher {
    static unsigned hash(Polynom::ComplexPolynom const& x) noexcept {
      unsigned out = 0;
      for (auto c : x._coeffs) {
        out ^= ComplexPolynom::getMonom(c).hash();
        out ^= ComplexPolynom::getCoeff(c).hash();
        out <<= 1;
      }
      return out;
    }
    static bool equals(Polynom::ComplexPolynom const& lhs, Polynom::ComplexPolynom const& rhs) {
      return lhs == rhs;
    }
  };
};

struct AnyPoly {
  
  template<class C>
  using poly = Polynom<num_traits<C>>;
  using self_t = Coproduct< poly<IntegerConstantType> , poly<RationalConstantType> , poly<RealConstantType> >;
  self_t self; 

  explicit AnyPoly(poly<IntegerConstantType>&& x) : self(self_t::variant<0>(std::move(x))) {
    CALL("AnyPoly(Int)")
  }
  explicit AnyPoly(poly<RationalConstantType>&& x ) : self(self_t::variant<1>(std::move(x))) {
    CALL("AnyPoly(Rat)")
  }
  explicit AnyPoly(poly<RealConstantType>&& x ) : self(self_t::variant<2>(std::move(x))) {
    CALL("AnyPoly(Real)")
  }

  template<class Const> const poly<Const>& ref() const;

  template<> const poly<IntegerConstantType>& ref<IntegerConstantType>() const 
  { return self.unwrap<0>();  }
  template<> const poly<RationalConstantType>& ref<RationalConstantType>() const 
  { return self.unwrap<1>();  }
  template<> const poly<RealConstantType>& ref<RealConstantType>() const 
  { return self.unwrap<2>();  }

  template<class Const> poly<Const>& ref_mut();

  template<> poly<IntegerConstantType>& ref_mut<IntegerConstantType>() 
  { return self.unwrap<0>();  }
  template<> poly<RationalConstantType>& ref_mut<RationalConstantType>()
  { return self.unwrap<1>();  }
  template<> poly<RealConstantType>& ref_mut<RealConstantType>() 
  { return self.unwrap<2>();  }

  template<class Const>
  void set(TermList t, Const c) {
    CALL("AnyPoly::set")
    return ref_mut<Const>().set(t,c);
  }

  template<class Const>
  Const get(TermList t) {
    CALL("AnyPoly::get")
    return ref_mut<Const>().get(t);
  }

  template<class Const, class Config>
  TermList toTerm() {
    CALL("AnyPoly::toTerm")
    return poly<Const>::template toTerm<Config>(ref_mut<Const>());
  }

  template<class Config>
  TermList toTerm_() {
    CALL("AnyPoly::toTerm_")
      //TODO replace with match

    if (self.is<0>()) {
      using ty = typename self_t::type<0>::value::Coeff;
      return toTerm<ty, Config>();

    } else if (self.is<1>()) {
      using ty = typename self_t::type<1>::value::Coeff;
      return toTerm<ty, Config>();

    } else {
      ASS(self.is<2>())
      using ty = typename self_t::type<2>::value::Coeff;
      return toTerm<ty, Config>();
    }
  }

  friend std::ostream& operator<<(std::ostream& out, const AnyPoly& x) {
    auto& self = x.self;
    if (self.is<0>()) {
      out << self.unwrap<0>();
    } else if (self.is<1>()) {
      out << self.unwrap<1>();
    } else {
      out << self.unwrap<2>();
    }
    return out;
  }
  AnyPoly& operator=(AnyPoly&&) = default;
  AnyPoly(AnyPoly&&) = default;
  explicit AnyPoly(const AnyPoly&) = default;
private:
};

class TermEvalResult : public Coproduct<TermList, AnyPoly> {
// class TermEvalResult : public Coproduct<TermList, AnyPoly> {
public:
  TermEvalResult() : Coproduct(Coproduct::template variant<0>(Kernel::TermList())) {}
  TermEvalResult(Coproduct     && super) : Coproduct(std::move(super)) {}
  TermEvalResult(Coproduct      & super) : Coproduct(          super ) {}
  TermEvalResult(Coproduct const& super) : Coproduct(          super ) {}
};

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Equality
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number> inline LitEvalResult interpret_equality(Literal* lit, bool polarity, TermList lhs, TermList rhs) {
  using Const = typename number::ConstantType;
  Const l;
  Const r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return LitEvalResult::template variant<1>(polarity == (l == r));
  } else {
    return LitEvalResult::template variant<0>(Literal::createEquality(lit->polarity(), lhs, rhs, number::sort));
  }
}

template<> LitEvalResult evaluateLit<Interpretation::EQUAL>(Literal* lit) {
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  if (lhs == rhs) return LitEvalResult::template variant<1>(lit->polarity());
  auto sort =  SortHelper::getEqualityArgumentSort(lit);
  switch (sort) {
    case Sorts::SRT_INTEGER:  return interpret_equality<num_traits<IntegerConstantType>>(lit, lit->polarity(), lhs, rhs);
    case Sorts::SRT_RATIONAL: return interpret_equality<num_traits<RationalConstantType>>(lit, lit->polarity(), lhs, rhs);
    case Sorts::SRT_REAL:     return interpret_equality<num_traits<RealConstantType>>(lit, lit->polarity(), lhs, rhs);
                             //TODO lift to term algebras
    default:
      return LitEvalResult::template variant<1>(Literal::createEquality(lit->polarity(), lhs, rhs, sort));
  }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Inequalities
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalIneq> LitEvalResult evaluateInequality(Literal* lit, bool strict, EvalIneq evalIneq) {
  ASS(lit->arity() == 2);
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  if (lhs == rhs) return LitEvalResult::template variant<1>(lit->polarity() != strict);
  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return LitEvalResult::template variant<1>(lit->polarity() == evalIneq(l, r));
  } else {
    return LitEvalResult::template variant<0>(lit);
  }
}

#define __IMPL_INEQ(Const, name, STRICT, op) \
  template<> LitEvalResult evaluateLit<num_traits<Const>::name ## I>(Literal* lit) \
  { return evaluateInequality<Const>(lit, STRICT, [](Const l, Const r) {return l op r;}); } \

#define IMPL_INEQUALTIES(Const) \
   /*                inequality| is strict? | operator */ \
  __IMPL_INEQ(Const, less      ,   true     ,  <        ) \
  __IMPL_INEQ(Const, leq       ,   false    ,  <=       ) \
  __IMPL_INEQ(Const, greater   ,   true     ,  >        ) \
  __IMPL_INEQ(Const, geq       ,   false    ,  >=       ) \


IMPL_INEQUALTIES(RationalConstantType)
IMPL_INEQUALTIES(RealConstantType) 
IMPL_INEQUALTIES(IntegerConstantType)

#undef  IMPL_NUM_EVALS
#undef  __IMPL_INEQ

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// INT_DIVIDES
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<> LitEvalResult evaluateLit<Interpretation::INT_DIVIDES>(Literal* lit) {
  return tryEvalConstant2<IntegerConstantType>(lit, [](IntegerConstantType l, IntegerConstantType r) { 
      return  (r % l) == 0;
  });
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// UNARY_MINUS 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number, class Config>
TermEvalResult evaluateUnaryMinus(TermEvalResult& inner) {
  auto out = inner.match<TermEvalResult>(
        [](const TermList& t) { 
        return TermEvalResult::template variant<1>(AnyPoly(
            Polynom<number>( number::constant(-1), t)
            ));
      }
      , [](const AnyPoly& p) {
        auto out = Polynom<number>::template poly_mul<Config>(
              Polynom<number>(number::constant(-1))
            , p.ref<typename number::ConstantType>());

        return TermEvalResult::template variant<1>(AnyPoly(std::move(out)));
      }
      );
  return out;
}

#define IMPL_UNARY_MINUS(Const) \
  IMPL_EVALUATE_FUN(num_traits<Const>::minusI, {\
    return evaluateUnaryMinus<num_traits<Const>, Config>(evaluatedArgs[0]);  \
  })

  IMPL_UNARY_MINUS(RealConstantType    )
  IMPL_UNARY_MINUS(RationalConstantType)
  IMPL_UNARY_MINUS(IntegerConstantType )

#undef IMPL_UNARY_MINUS


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// MULTIPLY
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number, class Config> TermEvalResult evaluateMul(TermEvalResult&& lhs, TermEvalResult&& rhs) 
{
  // TODO parametrize usePolyMul
  using poly = Polynom<number>;
  using Const = typename poly::Coeff;

  auto to_poly = [](TermEvalResult&& x) -> poly {
    return std::move(x).match<poly>(
        [](TermList&& t) { return poly(number::constant(1), t); }
      , [](AnyPoly&& p) { return std::move(p.ref_mut<Const>()); }
      );
  };

  return TermEvalResult::template variant<1>(AnyPoly(
        poly::template poly_mul<Config>(to_poly(std::move(lhs)), to_poly(std::move(rhs)))));
}


#define IMPL_MULTIPLY(Const) \
  IMPL_EVALUATE_FUN(num_traits<Const>::mulI, { \
    return evaluateMul<num_traits<Const>, Config>(std::move(evaluatedArgs[0]), std::move(evaluatedArgs[1])); \
  }) \

  IMPL_MULTIPLY(RealConstantType    )
  IMPL_MULTIPLY(RationalConstantType)
  IMPL_MULTIPLY(IntegerConstantType )

#undef IMPL_MULTIPLY


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// ADD 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number>
Polynom<number> evaluateAdd(TermEvalResult&& lhs, TermEvalResult&& rhs) {
  CALL("Polynom<number> evaluateAdd(TermEvalResult&& lhs, TermEvalResult&& rhs)")
  using Const = typename number::ConstantType;
  using poly = Polynom<number>;

  poly l = std::move(lhs).match<poly>(
        [](TermList && t) { return poly(number::constant(1), t); }
      , [](AnyPoly  && p) { return std::move(p.ref_mut<Const>()); }
      );

  poly r = std::move(rhs).match<poly>(
        [](TermList&& t) { return poly(number::constant(1), t); }
      , [](AnyPoly&& p) { return std::move(p.ref_mut<Const>()); }
      );
  
  return poly::poly_add(l, r);
}


#define IMPL_ADD(Const) \
  IMPL_EVALUATE_FUN(num_traits<Const>::addI, { \
    auto poly = evaluateAdd<num_traits<Const>>(std::move(evaluatedArgs[0]), std::move(evaluatedArgs[1])); \
    auto out = TermEvalResult::template variant<1>(AnyPoly(std::move(poly))); \
    return out; \
  }) \

  IMPL_ADD(RealConstantType    )
  IMPL_ADD(RationalConstantType)
  IMPL_ADD(IntegerConstantType )

#undef IMPL_ADD


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Number Constants 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class number>
TermEvalResult evaluateConst(typename number::ConstantType c) {
  return TermEvalResult::template variant<1>(AnyPoly(Polynom<number>(c)));
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Functions that are only handled for constants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#define IMPL_EVAL_UNARY(Const, INTER, expr) \
  IMPL_EVALUATE_FUN(Interpretation::INTER, { \
    return tryEvalConstant1<Const>(orig, evaluatedArgs, [] (Const x) { return expr; });  \
  } )

#define IMPL_EVAL_BINARY(Const, INTER, expr) \
  IMPL_EVALUATE_FUN(Interpretation::INTER, { \
    return tryEvalConstant2<Const>(orig, evaluatedArgs, [] (Const l, Const r) { return expr; }); \
  } )


/////////////////// Integer only functions

IMPL_EVAL_UNARY(IntegerConstantType, INT_ABS      , x >= 0 ? x : -x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_SUCCESSOR, x + 1          )

/////////////////// INT_QUOTIENT_E and friends

#define IMPL_QUOTIENT_REMAINDER(Const, NUM, SUFFIX) \
  IMPL_EVAL_BINARY(Const, NUM ##  _QUOTIENT_ ## SUFFIX,  l.quotient ## SUFFIX(r)) \
  IMPL_EVAL_BINARY(Const, NUM ## _REMAINDER_ ## SUFFIX,  l - (l.quotient ## SUFFIX (r)*r)) \

#define IMPL_QUOTIENT_REMAINDERS(Const, NUM) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, E) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, T) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, F) \
  IMPL_EVAL_BINARY(Const, NUM ## _MINUS, l - r) \

  IMPL_QUOTIENT_REMAINDERS(RealConstantType    , REAL)
  IMPL_QUOTIENT_REMAINDERS(RationalConstantType, RAT )
  IMPL_QUOTIENT_REMAINDERS(IntegerConstantType , INT )

#undef IMPL_QUOTIENT_REMAINDER
#undef IMPL_QUOTIENT_REMAINDERS

/////////////////// INT_FLOOR and friends

// have no effect for ints
IMPL_EVAL_UNARY(IntegerConstantType, INT_FLOOR   , x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_CEILING , x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_TRUNCATE, x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_ROUND   , x)

// same impl for fractionals
#define IMPL_FRAC_FLOOR_FRIENDS(Const, NUM) \
  IMPL_EVAL_UNARY(Const, NUM ## _FLOOR, x.floor()) \
  IMPL_EVAL_UNARY(Const, NUM ## _CEILING, x.ceiling()) \
  IMPL_EVAL_UNARY(Const, NUM ## _TRUNCATE, x.truncate()) \

  IMPL_FRAC_FLOOR_FRIENDS(RealConstantType    , REAL)
  IMPL_FRAC_FLOOR_FRIENDS(RationalConstantType, RAT)

#undef IMPL_EVAL_FRAC_FLOOR_FRIENDS
 
/////////////////// RAT_TO_INT and friends

#define IMPL_NUM_CVT(Const, NUM) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_INT, IntegerConstantType::floor(x)) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_RAT, RationalConstantType(x)) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_REAL, RealConstantType(x)) \

  IMPL_NUM_CVT(RealConstantType    , REAL)
  IMPL_NUM_CVT(RationalConstantType, RAT )
  IMPL_NUM_CVT(IntegerConstantType , INT )

#undef IMPL_NUM_CVT

/////////////////// QUOTIENT 
//
#define IMPL_QUOTIENT(Const, NUM) \
    IMPL_EVAL_BINARY(Const, NUM ## _QUOTIENT, l / r) \

  IMPL_QUOTIENT(RealConstantType    , REAL)
  IMPL_QUOTIENT(RationalConstantType, RAT )

#undef IMPL_QUOTIENT
 

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Helper functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalGround> LitEvalResult tryEvalConstant1(Literal* lit, EvalGround fun) {
  auto lhs = *lit->nthArgument(0);
  ConstantType l;
  if (theory->tryInterpretConstant(lhs, l)) {
    return LitEvalResult::template variant<1>(fun(l));
  } else {
    return LitEvalResult::template variant<0>(lit);
  }
}


template<class ConstantType, class EvalGround>
LitEvalResult tryEvalConstant2(Literal* lit, EvalGround fun) {
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return LitEvalResult::template variant<1>(fun(l,r));
  } else {
    return LitEvalResult::template variant<0>(lit);
  }
}


template<class ConstantType, class EvalGround>
TermEvalResult tryEvalConstant1(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun) {

  TermList lhs = evaluatedArgs[0].template unwrap<0>();
  ConstantType l;
  if (theory->tryInterpretConstant(lhs, l)) {
    return TermEvalResult::template variant<0>(TermList(theory->representConstant(fun(l))));
  } else {
    return TermEvalResult::template variant<0>(TermList(orig));
  }
}


template<class ConstantType, class EvalGround>
TermEvalResult tryEvalConstant2(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun) {

  TermList lhs = evaluatedArgs[0].template unwrap<0>();
  TermList rhs = evaluatedArgs[1].template unwrap<0>();

  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) 
      && theory->tryInterpretConstant(rhs, r)) {
    return TermEvalResult::template variant<0>(TermList(theory->representConstant(fun(l,r))));
  } else {
    return TermEvalResult::template variant<0>(TermList(orig));
  }
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Main literal evaluation
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Config> LitEvalResult PolynomialNormalizer<Config>::evaluate(Literal* lit) const {
  Stack<TermList> terms(lit->arity());
  for (int i = 0; i < lit->arity(); i++) {
    terms.push(evaluate(*lit->nthArgument(i)));
  }
  return evaluateStep(Literal::create(lit, terms.begin()));
}

template<class Config> LitEvalResult PolynomialNormalizer<Config>::evaluateStep(Literal* lit) const {
  CALL("PolynomialNormalizer::evaluateStep(Literal* term)")
  DEBUG("evaluating: ", lit->toString());

#define HANDLE_CASE(INTER) case Interpretation::INTER: return evaluateLit<Interpretation::INTER>(lit); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return LitEvalResult::template variant<0>(lit);
#define HANDLE_NUM_CASES(NUM) \
      IGNORE_CASE(NUM ## _IS_INT) /* TODO */ \
      IGNORE_CASE(NUM ## _IS_RAT) /* TODO */ \
      IGNORE_CASE(NUM ## _IS_REAL) /* TODO */ \
      HANDLE_CASE(NUM ## _GREATER) \
      HANDLE_CASE(NUM ## _GREATER_EQUAL) \
      HANDLE_CASE(NUM ## _LESS) \
      HANDLE_CASE(NUM ## _LESS_EQUAL) 

  //TODO create function theory->tryInterpret(Predicate|Function)
  auto sym = env.signature->getPredicate(lit->functor());
  if (sym->interpreted()) {
    auto inter = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();

    switch (inter) {
      /* polymorphic */
      HANDLE_CASE(EQUAL)

      /* common number predicates */
      HANDLE_NUM_CASES(INT)
      HANDLE_NUM_CASES(RAT)
      HANDLE_NUM_CASES(REAL)

      /* integer predicates */
      HANDLE_CASE(INT_DIVIDES)

      default:
        // DBG("WARNING: unexpected interpreted predicate: ", lit->toString())
        ASSERTION_VIOLATION
        return LitEvalResult::template variant<0>(lit);
    }
  } else {
    return LitEvalResult::template variant<0>( lit );
  }

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Main Term
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////


template<class Config> TermList PolynomialNormalizer<Config>::evaluate(TermList term) const {
  if (term.isTerm()) {
    return evaluate(term.term()); 
  } else {
    ASS_REP(term.isVar(), term);
    /* single variables can't be simplified */
    return term;
  }
}

template<class Config> TermList PolynomialNormalizer<Config>::evaluate(Term* term) const {
  CALL("PolynomialNormalizer::evaluate(Term* term)")
  DEBUG("evaluating ", term->toString())
  static Map<Term*, TermEvalResult> memo;

  static Stack<TermList*> recursion(8);

  static Stack<Term*> terms(8);
  static vector<TermEvalResult> args;

  args.clear();
  recursion.reset();
  terms.reset();

  recursion.push(term->args());
  terms.push(term);

  TermList* cur;
  while (!recursion.isEmpty()) {

    cur = recursion.pop();

    if (!cur->isEmpty()) {

      recursion.push(cur->next());

      if(cur->isVar()) {
        // variables are not evaluated
        args.emplace_back(TermEvalResult::template variant<0>(*cur));

      } else {
        ASS(cur->isTerm());

        Term* t = cur->term();

        auto cached = memo.getPtr(t);
        if (cached == nullptr) {
           terms.push(t);
           recursion.push(t->args());
        } else {
          args.emplace_back(TermEvalResult(*cached)); 
        }
      }


    } else /* cur->isEmpty() */ { 

      ASS(!terms.isEmpty()) 

      Term* orig=terms.pop();

      TermEvalResult& res = memo.getOrInit(std::move(orig), 
          [&](TermEvalResult* toInit){ 

            TermEvalResult* argLst = 0;
            if (orig->arity() != 0) {
              argLst=&args[args.size() - orig->arity()];
            }

            ::new(toInit) TermEvalResult(evaluateStep(orig,argLst));
          });

      DEBUG("evaluated: ", orig->toString(), " -> ", res);

      args.resize(args.size() - orig->arity());
      args.emplace_back(TermEvalResult(res));
      
    }

  }
  ASS_REP(recursion.isEmpty(), recursion)
    

  ASS(args.size() == 1);
  TermEvalResult out = TermEvalResult::template variant<0>( TermList() );
  std::move(std::make_move_iterator(args.begin()),
            std::make_move_iterator(args.end()),
            &out);
  auto out_ = std::move(out).match<TermList>(
        [](TermList&& l) { return l; }
      , [](AnyPoly&&  p) { return p.template toTerm_<Config>(); }
      ); 
  return out_;
}


template<class Config>
inline TermList createTerm(unsigned fun, const Signature::Symbol& sym, TermEvalResult* evaluatedArgs) {
  Stack<TermList> args(sym.arity());

  auto& op = *sym.fnType();
  auto arity = op.arity();
  for (int i = 0; i < arity; i++) {
    args.push(std::move(evaluatedArgs[0]).match<TermList>(
        [](TermList&& t) {return t;}
      , [](AnyPoly&& p) { return p.template toTerm_<Config>(); }
        ));
  }
  return TermList(Term::create(fun, arity, args.begin()));
}

template<class Config> TermEvalResult PolynomialNormalizer<Config>::evaluateStep(Term* orig, TermEvalResult* args) const {
  CALL("PolynomialNormalizer::evaluateStep(Term* orig, TermEvalResult* args)")

#define HANDLE_CASE(INTER) case Interpretation::INTER: return FunctionEvaluator<Interpretation::INTER>::evaluate<Config>(orig, args); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return TermEvalResult::template variant<0>(createTerm<Config>(functor, *sym, args));


#define HANDLE_CONSTANT_CASE(Num) \
  { \
    Num ## ConstantType c; \
    if (theory->tryInterpretConstant(orig, c)) { \
      return evaluateConst<num_traits<Num ## ConstantType>>(c); \
    } \
  } \

#define HANDLE_NUM_CASES(NUM) \
    HANDLE_CASE(NUM ## _UNARY_MINUS) \
    HANDLE_CASE(NUM ## _PLUS) \
    HANDLE_CASE(NUM ## _MINUS) \
    HANDLE_CASE(NUM ## _MULTIPLY) \
    HANDLE_CASE(NUM ## _QUOTIENT_E) \
    HANDLE_CASE(NUM ## _QUOTIENT_T) \
    HANDLE_CASE(NUM ## _QUOTIENT_F) \
    HANDLE_CASE(NUM ## _REMAINDER_E) \
    HANDLE_CASE(NUM ## _REMAINDER_T) \
    HANDLE_CASE(NUM ## _REMAINDER_F) \
    HANDLE_CASE(NUM ## _FLOOR) \
    HANDLE_CASE(NUM ## _CEILING) \
    HANDLE_CASE(NUM ## _TRUNCATE) \
    HANDLE_CASE(NUM ## _TO_INT) \
    HANDLE_CASE(NUM ## _TO_RAT) \
    HANDLE_CASE(NUM ## _TO_REAL) \

  auto functor = orig->functor();
  auto sym = env.signature->getFunction(functor);

  if (sym->interpreted()) {
    auto inter = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();
    switch (inter) {

      /* common number functions*/
      HANDLE_NUM_CASES(INT)
      HANDLE_NUM_CASES(RAT)
      HANDLE_NUM_CASES(REAL)

      /* integer functions */
      HANDLE_CASE(INT_SUCCESSOR)
      HANDLE_CASE(INT_ABS)

      /* rational functions */
      HANDLE_CASE(RAT_QUOTIENT)
      IGNORE_CASE(RAT_ROUND)  //TODO

      /* real functions */
      HANDLE_CASE(REAL_QUOTIENT)
      IGNORE_CASE(REAL_ROUND)  //TODO

      /* ignored */
      IGNORE_CASE(ARRAY_SELECT)
      IGNORE_CASE(ARRAY_BOOL_SELECT)
      IGNORE_CASE(ARRAY_STORE)

      default:
        if (theory->isInterpretedNumber(orig)) {
          HANDLE_CONSTANT_CASE(Integer)
          HANDLE_CONSTANT_CASE(Rational)
          HANDLE_CONSTANT_CASE(Real)
        }
        ASS_REP(false, "unexpected interpreted function: " + orig->toString())
        // return TermList(Term::create(orig, args));
        return TermEvalResult::template variant<0>(createTerm<Config>(functor, *sym, args));

    }

  } else {
      return TermEvalResult::template variant<0>(createTerm<Config>(functor, *sym, args));
  }
}

// TODO
// - include division (?)
// - include binary minus
// - integrate in simplification rule (evaluation simpl)
// - integrate in rebalancing elimination
//     test this case:
//     - eq(mul(2, a), add(x, x)) =====>  eq(a, x)

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}

#define INSTANTIATE_STATIC(value) \
  template<> decltype(value) value = decltype(value)();

#define INSTANTIATE_STATICS(Integer) \
  INSTANTIATE_STATIC(Kernel::Monom  <Kernel::num_traits<Kernel::Integer ## ConstantType>>::monoms  ) \
  INSTANTIATE_STATIC(Kernel::Polynom<Kernel::num_traits<Kernel::Integer ## ConstantType>>::polynoms)

INSTANTIATE_STATICS(Integer)
INSTANTIATE_STATICS(Rational)
INSTANTIATE_STATICS(Real)
