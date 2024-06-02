/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file RobSubstitution.hpp
 * Defines class RobSubstitution.
 *
 */

#ifndef __RobSubstitution__
#define __RobSubstitution__

#include "Forwards.hpp"
#include "Kernel/Polynomial.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Recycled.hpp"
#include "Term.hpp"
#include "Lib/Hash.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/TypedTermList.hpp"
#include <initializer_list>

#if VDEBUG
#include <iostream>
#include "Lib/VString.hpp"
#endif


const int GLUE_INDEX=-3;
const int SPECIAL_INDEX=-2;
const int UNBOUND_INDEX=-1;
namespace Kernel
{

template<class TermSpecOrList, class VarBankOrInt>
class RobSubstitution;

struct VarSpec
{
  VarSpec() {}
  VarSpec(unsigned var, VarBank bank) : var(var), bank(bank) {}

  friend std::ostream& operator<<(std::ostream& out, VarSpec const& self);

  /** number of variable */
  unsigned var;
  /** index of variable bank */
  VarBank bank;

  auto asTuple() const { return std::tie(var, bank); }
  IMPL_COMPARISONS_FROM_TUPLE(VarSpec)

  unsigned defaultHash () const { return HashUtils::combine(var , bank); }
  unsigned defaultHash2() const { return HashUtils::combine(bank, var  ); }
};

struct TermSpec {
  TermSpec() {}

  TermSpec(TermList t, VarBank i) : term(t), bank(t.isSpecialVar() ? VarBank::SPECIAL_BANK : i) {}
  TermSpec(VarSpec v) : term(TermList::var(v.var)), bank(v.bank) {}

  auto asTuple() const -> decltype(auto) { return std::tie(term, bank); }
  IMPL_COMPARISONS_FROM_TUPLE(TermSpec)
  IMPL_HASH_FROM_TUPLE(TermSpec)

  TermList term;
  VarBank bank;
  bool sameTermContent(const TermSpec& ts) const
  {
    bool termSameContent=term.sameContent(&ts.term);
    if(!termSameContent && term.isTerm() && term.term()->isLiteral() &&
      ts.term.isTerm() && ts.term.term()->isLiteral()) {
      const Literal* l1=static_cast<const Literal*>(term.term());
      const Literal* l2=static_cast<const Literal*>(ts.term.term());
      if(l1->functor()==l2->functor() && l1->arity()==0) {
        return true;
      }
    }
    if(!termSameContent) {
      return false;
    }
    return bank==ts.bank || term.isSpecialVar() ||
      (term.isTerm() && (
  (term.term()->shared() && term.term()->ground()) ||
   term.term()->arity()==0 ));
  }

  friend std::ostream& operator<<(std::ostream& out, TermSpec const& self);

  bool isVar() const { return term.isVar(); }
  VarSpec varSpec() const { return VarSpec(term.var(), term.isSpecialVar() ? VarBank::SPECIAL_BANK : bank); }
  bool isTerm() const { return term.isTerm(); }

  TermSpec termArgSort(unsigned i) const { return TermSpec(SortHelper::getTermArgSort(term.term(), i), bank); }

  unsigned nTypeArgs() const { return term.term()->numTermArguments(); }
  unsigned nTermArgs() const { return term.term()->numTermArguments(); }
  unsigned nAllArgs() const { return term.term()->arity(); }

  TermSpec termArg(unsigned i) const { return TermSpec(this->term.term()->termArg(i), this->bank); }
  TermSpec typeArg(unsigned i) const { return TermSpec(this->term.term()->typeArg(i), this->bank); }
  TermSpec anyArg (unsigned i) const { return TermSpec(*this->term.term()->nthArgument(i), this->bank); }

  auto typeArgs() const { return range(0, nTypeArgs()).map([this](auto i) { return typeArg(i); }); }
  auto termArgs() const { return range(0, nTermArgs()).map([this](auto i) { return termArg(i); }); }
  auto allArgs()  const { return range(0, nAllArgs()).map([this](auto i) { return anyArg(i); }); }

  bool deepEqCheck(const TermSpec& t2) const {
    TermSpec const& t1 = *this;
    if (t1.term.sameContent(t2.term)) {
      return t1.isVar() ? t1.bank == t2.bank
                        : (t1.bank == t2.bank || t1.term.term()->ground());
    } else {
      if (t1.isTerm() != t2.isTerm()) return false;
      if (t1.isVar()) {
        ASS(t2.isVar() && (t1.term.var() != t2.term.var() || t1.term.isSpecialVar() != t2.term.isSpecialVar()));
        return false;
      }
      return t1.functor() == t2.functor() 
        && t1.allArgs().zip(t2.allArgs()).all([](auto pair) { return pair.first.deepEqCheck(pair.second); });
    }
  }


  TermList::Top top() const { return this->term.top(); }
  unsigned functor() const { return term.term()->functor(); }

  bool isSort() const
  { return this->term.term()->isSort(); }

  bool sortIsBoolOrVar() const
  { 
    if (!isTerm()) return false;
    auto fun = env.signature->getFunction(functor());
    auto op = fun->fnType();
    TermList res = op->result();
    return res.isVar() || res == AtomicSort::boolSort();
  }

  bool isNumeral() const { return theory->isInterpretedNumber(this->term); }

  bool definitelyGround() const 
  { return this->term.isTerm() 
        && this->term.term()->shared() 
        && this->term.term()->ground(); }

  unsigned groundWeight() const 
  {
    ASS(definitelyGround());
    return this->term.weight();
  }

  template<class Deref>
  static int compare(TermSpec const& lhs, TermSpec const& rhs, Deref deref) {
    Recycled<Stack<std::pair<TermSpec, TermSpec>>> todo;
    todo->push(std::make_pair(lhs,rhs));
    while (todo->isNonEmpty()) {
      auto lhs_ = std::move(todo->top().first);
      auto rhs_ =           todo->pop().second;
      auto& lhs = deref(lhs_);
      auto& rhs = deref(rhs_);

      if (lhs.isTerm() != rhs.isTerm()) {
        return lhs.isVar() ? -1 : 1;

      } else {
        if (lhs.isTerm()) {
          if (lhs.functor() != rhs.functor()) {
            return lhs.functor() < rhs.functor() ? -1 : 1;
          } else {
            todo->loadFromIterator(lhs.allArgs().zip(rhs.allArgs()));
          }
        } else {
          ASS(lhs.isVar() && rhs.isVar());
          auto v1 = lhs.varSpec();
          auto v2 = rhs.varSpec();
          if (v1 != v2) {
            return std::tie(v1.var, v1.index) < std::tie(v2.var, v2.index) ? -1 : 1;
          }
        }
      }
    }
    return 0;
  }
};
static_assert(std::is_trivially_copyable_v<TermSpec>, "TermSpec is trivially copyable");

/** A wrapper around TermSpec that automatically dereferences the TermSpec with respect to some RobSubstition when 
 * used with BottomUpEvaluation.  This means for example if we evaluate some TermSpec * `g(X, Y)` in a context 
 * `{ X -> a, Y -> f(X) }` it behaves as if we would evaluate `g(a,f(a))`.  */
struct AutoDerefTermSpec
{
  TermSpec term;

  AutoDerefTermSpec(TermSpec const& t, RobSubstitution const* s);
  explicit AutoDerefTermSpec(AutoDerefTermSpec const& other) : term(other.term) {}
  AutoDerefTermSpec(AutoDerefTermSpec && other) = default;
  friend std::ostream& operator<<(std::ostream& out, AutoDerefTermSpec const& self);

  struct Context 
  { RobSubstitution const* subs; };
};

/* a Memo to be used with BottomUpEvaluation and AutoDerefTermSpec that only memorizes the result for non-variable subterms. */
template<class Result>
class OnlyMemorizeNonVar 
{
  Map<TermSpec, Result> _memo;
public:
  OnlyMemorizeNonVar(OnlyMemorizeNonVar &&) = default;
  OnlyMemorizeNonVar& operator=(OnlyMemorizeNonVar &&) = default;
  OnlyMemorizeNonVar() : _memo() {}

  auto memoKey(AutoDerefTermSpec const& arg) -> Option<TermSpec>
  { 
    if (arg.term.term.isTerm()) {
      return some(arg.term);
    } else {
      return {};
    }
  }

  Option<Result> get(AutoDerefTermSpec const& arg)
  { 
    auto key = memoKey(arg);
    return key.isSome()
       ? _memo.tryGet(*key).toOwned()
       : Option<Result>(); 
  }

  template<class Init> Result getOrInit(AutoDerefTermSpec const& orig, Init init)
  { 
    auto key = memoKey(orig);
    return key.isSome() ? _memo.getOrInit(*key, init)
                        : init(); 
  }
  void reset() { _memo.reset(); }
};

template<class T, class... Other>
constexpr bool allow_types = (std::is_same_v<T, Other> || ...);

template<class TermSpecOrList, class VarBankOrInt>
class UnificationConstraint
{
  static_assert(allow_types<TermSpecOrList, TermSpec, TermList>, "Only allow TermSpec and TermList");

  using RobSubst = RobSubstitution<TermSpecOrList,VarBankOrInt>;

public:
  UnificationConstraint() {}
  USE_ALLOCATOR(UnificationConstraint)
  auto asTuple() const -> decltype(auto) { return std::tie(_t1, _t2, _sort); }
  IMPL_COMPARISONS_FROM_TUPLE(UnificationConstraint);
  IMPL_HASH_FROM_TUPLE(UnificationConstraint);

  UnificationConstraint(TermSpecOrList t1, TermSpecOrList t2, TermSpec sort)
  : _t1(t1), _t2(t2), _sort(sort)
  {}

  Option<Literal*> toLiteral(RobSubst& s) {
    auto t1 = s.apply(_t1);
    auto t2 = s.apply(_t2);
    auto sort = _sort.toTerm(s);
    return t1 == t2
        ? Option<Literal*>()
        : Option<Literal*>(Literal::createEquality(false, t1, t2, sort));
  }

  TermSpecOrList const& lhs() const { return _t1; }
  TermSpecOrList const& rhs() const { return _t2; }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraint<TermSpecOrList, VarBankOrInt> const& self)
  { return out << self._t1 << " ?= " << self._t2; }

private:
  TermSpecOrList _t1;
  TermSpecOrList _t2;
  TermSpec _sort;
};

template<class TermSpecOrList, class VarBankOrInt>
class UnificationConstraintStack
{
  using Constraint = UnificationConstraint<TermSpecOrList,VarBankOrInt>;
  using RobSubst = RobSubstitution<TermSpecOrList,VarBankOrInt>;

  Stack<Constraint> _cont;
public:
  USE_ALLOCATOR(UnificationConstraintStack)
  UnificationConstraintStack() : _cont() {}
  UnificationConstraintStack(UnificationConstraintStack&&) = default;
  UnificationConstraintStack& operator=(UnificationConstraintStack&&) = default;

  auto iter() const
  { return iterTraits(_cont.iter()); }

  Recycled<Stack<Literal*>> literals(RobSubst& s) {
    Recycled<Stack<Literal*>> out;
    out->reserve(_cont.size());
    out->loadFromIterator(literalIter(s));
    return out;
  }

  // returns the maximum number of constraints of this stack. this is not equal to the actual number of constraints it will hold, as constraints
  // might become trivial (i.e. of the form t != t) after applying the substitution, so they will be filtered out when calling literals(RobSubstitution&)
  unsigned maxNumberOfConstraints() { return _cont.size(); }

  auto literalIter(RobSubst& s)
  { return iterTraits(_cont.iter())
        .filterMap([&](auto& c) { return c.toLiteral(s); }); }

  friend std::ostream& operator<<(std::ostream& out, UnificationConstraintStack const& self)
  { return out << self._cont; }

  void reset() { _cont.reset(); }
  bool keepRecycled() const { return _cont.keepRecycled() > 0; }

  bool isEmpty() const
  { return _cont.isEmpty(); }

  void add(Constraint c, Option<BacktrackData&> bd) {
    // DEBUG("introduced constraint: ", c)
    _cont.push(c);
    if (bd) {
      bd->addClosure([this]() { _cont.pop(); });
    }
  }

  Constraint pop(Option<BacktrackData&> bd) {
    auto old = _cont.pop();
    if (bd) {
      bd->addClosure([this, old]() mutable { _cont.push(std::move(old)); });
    }
    return old;
  }
};

using namespace Lib;

class AbstractingUnifier;
// class UnificationConstraint;

template<class TermSpecOrList, class VarBankOrInt>
class RobSubstitution
:public Backtrackable
{
  friend class AbstractingUnifier;
  friend class UnificationConstraint<TermSpecOrList, VarBankOrInt>;

  using Constraint = UnificationConstraint<TermSpecOrList,VarBankOrInt>;
  using ConstraintStack = UnificationConstraintStack<TermSpecOrList,VarBankOrInt>;
  using RobSubst = RobSubstitution<TermSpecOrList,VarBankOrInt>;

  DHMap<VarSpec, TermSpec> _bindings;
  mutable DHMap<VarSpec, unsigned> _outputVarBindings;
  mutable bool _startedBindingOutputVars;
  mutable unsigned _nextUnboundAvailable;
  mutable unsigned _nextGlueAvailable;
  DHMap<TermSpec, unsigned> _gluedTerms;
  mutable OnlyMemorizeNonVar<TermList> _applyMemo;

public:
  USE_ALLOCATOR(RobSubstitution);
  
  RobSubstitution() 
    : _startedBindingOutputVars(false)
    , _nextUnboundAvailable(0) 
    , _nextGlueAvailable(0) 
    , _gluedTerms() 
  {}
  virtual ~RobSubstitution() = default;

  /* When a `RobSubstitution` is applied to a Term by default the variables in the resulting
   * Term will be in a new variable index, that starts mapping the first occurring
   * variable in the output to X0, the second one to X1, ....
   * In some cases this behaviour should be changed. For example if we a variables sigma such that
   * `(s)sigma = t` using `RobSubstitution::match` we want that the variables are not assigned to a new
   * index but to the same one as `t`. Therefore this function lets you set the output index of the
   * substitution.
   *
   * Be aware that this is not possible when:
   * - applying the substitution to variables that are not in the output index, that were not bound in the
   *   substitution (i.e. part of generalization operations, etc.)
   * - computing unifications
   */
  void setOutputIndex(VarBankOrInt idx) { _outputIndex = idx; }

  bool unify(TermSpecOrList t1, TermSpecOrList t2
#if VHOL
             , bool applicativeUnify = false
#endif
             );

  SubstIterator matches(Literal* base, VarBank baseBank, Literal* instance, VarBank instanceBank, bool complementary);
  SubstIterator unifiers(Literal* l1, VarBank l1Bank, Literal* l2, VarBank l2Bank, bool complementary);


  bool match(TermList base, VarBank baseBank, TermList instance, VarBank instanceBank);

  bool unifyArgs(Term* t1, VarBank bank1, Term* t2, VarBank bank2);
  bool matchArgs(Term* base, VarBank baseBank, Term* instance, VarBank instanceBank);

  void denormalize(const Renaming& normalizer, VarBank normalBank, VarBank denormalizedBank);
  bool isUnbound(VarSpec v) const;

  /** introduces a new "glue" variable, and binds it to forTerm. 
   * Glue variables live in their own namespace that is only used within this rob substitution. They are used only to represent subterms of other terms in the substitution.
   * This is useful in cases where we want to create terms that contain two subterms of different variable banks in e.g. Unification with Abstraction:
   *
   * Say we want to unify
   * x + f(y)    <- var bank 0
   * and   
   * f(y)        <- var bank 1
   *
   * Then an mgu is x -> -f(y/0) + f(y/1)
   * This cannot be directly represented in vampire as our TermSpec can only hold 1 variable bank per term, and not multiple per subterm. So what we want to do instead 
   * is introduce two new "glue" variables varibles G0, G1
   *
   * G0 -> -f(y)/0
   * G1 ->  f(y)/1
   *
   * and return as mgu
   * {x -> G0 + G1, G0 -> -f(y)/0, G1 -> f(y)/1}
   */
  VarSpec introGlueVar(TermSpec forTerm);

  /* creates a new TermSpec with the given arguments `args` which all need to be of type `TermSpec`. If any of the argumetns have different variable banks "glue" variable are introduced. See the function `introGlueVar` for that. */
  template<class... Args>
  TermSpec createTerm(unsigned functor, Args... args)
  {
    TermSpec out;
    if (iterItems(args...).count() == 0) {
      return TermSpec(TermList(Term::create(functor, 0, nullptr)), VarBank::DEFAULT_BANK);
    }
    auto firstBank = iterItems(args...).tryNext().unwrap().bank;
    if (iterItems(args...).all([&](auto a) { return a.bank == firstBank; })) {
      return TermSpec(TermList(Term::create(functor, {args.term...})), firstBank);
    } else {
      return TermSpec(TermList(Term::create(functor, { 
              (args.bank == VarBank::GLUE_BANK ? args.term
                                               : TermList::var(introGlueVar(args).var))...
              })), VarBank::GLUE_BANK);
    }
  }

  void reset()
  {
    _bindings.reset();
    _outputVarBindings.reset();
    _startedBindingOutputVars = false;
    _nextUnboundAvailable=0;
    _nextGlueAvailable=0;
    _gluedTerms.reset();
    _applyMemo.reset();
  }
  bool keepRecycled() const { return _bindings.keepRecycled() || _outputVarBindings.keepRecycled(); }

  /**
   * Bind special variable to a specified term
   *
   * Calls to this method must happen before calls to any
   * other methods. Also no special variables can occur in
   * binding term, as no occur-check is performed.
   */
  void bindSpecialVar(unsigned var, TermList t, VarBank bank)
  {
    VarSpec vs(var, VarBank::SPECIAL_BANK);
    ASS(!_bindings.find(vs));
    bind(vs, TermSpec(t, bank));
  }

  TermList::Top getSpecialVarTop(unsigned specialVar) const;
  TermList apply(TermList t, VarBank bank) const;
  Literal* apply(Literal* lit, VarBank bank) const;
  TypedTermList apply(TypedTermList t, VarBank bank) const { return TypedTermList(apply(TermList(t), bank), apply(t.sort(), bank)); }
  Stack<Literal*> apply(Stack<Literal*> cl, VarBank bank) const;
  size_t getApplicationResultWeight(TermList t, VarBank bank) const;
  size_t getApplicationResultWeight(Literal* lit, VarBank bank) const;

  bool isEmpty() const { return _bindings.size() == 0 && _outputVarBindings.size() == 0; }

  friend std::ostream& operator<<(std::ostream& out, RobSubstitution const& self);
  std::ostream& output(std::ostream& out, bool deref) const;

  friend std::ostream& operator<<(std::ostream& out, VarSpec const& self)
  {
    if(self.bank == VarBank::SPECIAL_BANK) {
      return out << "S" << self.var;
    } else {
      return out << "X" << self.var << "/" << self.bank;
    }
  }


  RobSubstitution(RobSubstitution&& obj) = default;
  RobSubstitution& operator=(RobSubstitution&& obj) = default;
  TermSpec const& derefBound(TermSpec const& v) const;
  unsigned findOrIntroduceOutputVariable(VarSpec v) const;
protected:
  VarBankOrInt _outputIndex;
private:
  TermList apply(TermSpec);
  RobSubstitution(const RobSubstitution& obj) = delete;
  RobSubstitution& operator=(const RobSubstitution& obj) = delete;

  template<class T, class H1, class H2>
  void bind(DHMap<VarSpec, T, H1, H2>& map, const VarSpec& v, T b);
  void bind(const VarSpec& v, TermSpec b);
  void bindVar(const VarSpec& var, const VarSpec& to);
  bool match(TermSpec base, TermSpec instance);
  bool unify(TermSpec t1, TermSpec t2);
  bool occurs(VarSpec const& vs, TermSpec const& ts);

  friend std::ostream& operator<<(std::ostream& out, RobSubstitution const& self)
  { return out << "(" << self._bindings << ", " << self._outputVarBindings << ")"; }

  template<class Fn>
  SubstIterator getAssocIterator(RobSubstitution* subst, Literal* l1, VarBank l1Bank, Literal* l2, VarBank l2Bank, bool complementary);

  template<class Fn>
  struct AssocContext;
  template<class Fn>
  class AssocIterator;

  struct MatchingFn;
  struct UnificationFn;

};

inline AutoDerefTermSpec::AutoDerefTermSpec(TermSpec const& t, RobSubstitution const* s) : term(s->derefBound(t)) {}

};

namespace Lib {
  template<>
  struct BottomUpChildIter<Kernel::AutoDerefTermSpec>
  {
    using Item = Kernel::AutoDerefTermSpec;
    Item _self;
    unsigned _arg;

    BottomUpChildIter(Item const& self, Kernel::AutoDerefTermSpec::Context c) : _self(Item(self)), _arg(0) {}
 
    Item const& self() { return _self; }

    Item next(Kernel::AutoDerefTermSpec::Context c)
    { return Kernel::AutoDerefTermSpec(_self.term.anyArg(_arg++), c.subs); }

    bool hasNext(Kernel::AutoDerefTermSpec::Context c)
    { return _self.term.isTerm() && _arg < _self.term.nAllArgs(); }

    unsigned nChildren(Kernel::AutoDerefTermSpec::Context c)
    { return _self.term.isTerm() ? _self.term.nAllArgs() : 0; }
  };

} // namespace Lib

#endif /*__RobSubstitution__*/
