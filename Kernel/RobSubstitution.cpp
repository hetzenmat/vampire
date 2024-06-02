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
 * @file RobSubstitution.cpp
 * Implements polynomial modification of the Robinson unification algorithm.
 */


#include "RobSubstitution.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Output.hpp"
#include "Debug/Tracer.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/Term.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"

#include "Renaming.hpp"
#include "SortHelper.hpp"
#include "TermIterators.hpp"

namespace Kernel
{

using namespace std;
using namespace Lib;

std::ostream& operator<<(std::ostream& out, TermSpec const& self)
{ return out << self.term << "/" << self.bank; }



/**
 * Unify @b t1 and @b t2, and return true iff it was successful.
 */
template<class TermSpecOrList, class V>
bool RobSubstitution<TermSpecOrList,V>::unify( TermSpecOrList t1
                                             , TermSpecOrList t2
#if VHOL
                                             , bool applicativeUnify
#endif
)
{
#define DEBUG_UNIFY(lvl, ...) if (lvl < 0) DBG("unify: ", __VA_ARGS__)
  DEBUG_UNIFY(0, *this, ".unify(", t1, ",", t2, ")")

  if(sameTermContent(t1,t2)) {
    return true;
  }

  BacktrackData localBD;
  bdRecord(localBD);

  static Stack<Constraint> toDo(64);
  ASS(toDo.isEmpty());
  toDo.push(Constraint(t1, t2));

  // Save encountered unification pairs to avoid
  // recomputing their unification
  Recycled<DHSet<Constraint>> encountered;

#if VHOL
  auto containsLooseIndex = [](TermList t){
    if(env.getMainProblem()->isHigherOrder()) {
      // should never reach here from a tree
      // currently we only reach this point by a call to unifiers
      // from condensation
      ASS(t.isVar() || t.term()->shared());
      // we don't need to dereference any bound variables
      // since we should never be binding a variable to a term that contains a loose index
      return t.containsLooseIndex();
    }
    return false;
  };
#endif

  auto pushTodo = [&](auto pair) {
    // we unify each subterm pair at most once, to avoid worst-case exponential runtimes
    // in order to safe memory we do ot do this for variables.
    // (Note by joe:  didn't make this decision, but just keeping the implemenntation
    // working as before. i.e. as described in the paper "Comparing Unification
    // Algorithms in First-Order Theorem Proving", by Krystof and Andrei)
    if (pair.lhs().isVar() && isUnbound(pair.lhs()) &&
        pair.rhs().isVar() && isUnbound(pair.rhs())) {
      toDo.push(std::move(pair));
    } else if (!encountered->find(pair)) {
      encountered->insert(pair);
      toDo.push(pair);
    }
  };

  bool mismatch=false;
  // Iteratively resolve unification pairs in toDo
  // the current pair is always in t1 and t2 with their dereferenced
  // version in dt1 and dt2
  while (toDo.isNonEmpty()) {
    auto x = toDo.pop();
    TermSpecOrList const& dt1 = derefBound(x.lhs());
    TermSpecOrList const& dt2 = derefBound(x.rhs());
    DEBUG_UNIFY(1, "next pair: ", tie(dt1, dt2))
    // If they have the same content then skip
    // (note that sameTermContent is best-effort)

    if (sameTermContent(dt1,dt2)) {
      // Deal with the case where eithe rare variables
      // Do an occurs-check and note that the variable
      // cannot be currently bound as we already dereferenced
    } else if(dt1.isVar() && !occurs(dt1, dt2)
#if VHOL
             && (!applicativeUnify || !containsLooseIndex(dt2))
#endif
    ) {
      bind(dt1, dt2);

    } else if (dt2.isVar() && !occurs(dt2, dt1)
#if VHOL
             && (!applicativeUnify || !containsLooseIndex(dt1))
#endif
    ) {
      bind(dt2, dt1);

    } else if(dt1.isTerm() && dt2.isTerm() && dt1.term()->functor() == dt2.term()->functor()) {

      for (unsigned i = 0; i < dt1.term()->arity(); i++) {
        pushTodo(Constraint(dt1.nthArg(i), dt2.nthArg(i)));
      }

    } else {
      mismatch = true;
      break;
    }

    ASS(!mismatch);
  }

  if(mismatch) {
    toDo.reset();
  }

  bdDone();

  if(mismatch) {
    localBD.backtrack();
  } else {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  }

  DEBUG_UNIFY(0, *this)
  return !mismatch;
}

template<class TermSpecOrList, class VarBankOrInt>
bool RobSubstitution<TermSpecOrList,VarBankOrInt>::match(TermSpecOrList base, TermSpecOrList instance, VarBankOrInt baseBank)
{
#define DEBUG_MATCH(lvl, ...) if (lvl < 0) DBG("match: ", __VA_ARGS__)

  if(sameTermContent(base,instance)) { return true; }

  bool mismatch=false;
  BacktrackData localBD;
  bdRecord(localBD);

  static Stack<Constraint> toDo(64);
  ASS(toDo.isEmpty());
  toDo.push(Constraint(base, instance));

  auto quickTests = [](TermList bt, TermList it){
    if(bt.isTerm() && bt.term()->shared() && it.isTerm() && it.term()->shared()){
      if(bt.term()->ground()){ return bt == it; }
      return bt.term()->weight() <= it.term()->weight();
    }
    return true;
  };

  auto canBind = [&](TermSpecOrList t)
  { return t.isVar() && t.bank() == baseBank; };

  auto dealWithSpec = [&](TermSpecOrList spec, TermSpecOrList term, bool instance){
    auto binding = _bank.find(spec);
    if(binding) {
      TermSpecOrList t = binding.unwrap();
      toDo.push(instance ? Constraint(term,t) : Constraint(t,term));
    } else {
      bind(spec, term);
    }
  };

  auto canCompare = [](TermSpecOrList t)
  { return !t.isSpecialVar() && (t.isVar() || t.term()->shared()); };

  // Iteratively resolve matching pairs in toDo
  while (toDo.isNonEmpty()) {
    auto x = toDo.pop();
    TermSpecOrList bt = x.lhs();
    TermSpecOrList it = x.rhs();
    DEBUG_MATCH(1, "next pair: ", tie(bt, it))

    if(!quickTests(bt,it)){
      DEBUG_MATCH(1, "Rejected by quick tests")
      mismatch = true;
      break;
    }

    if(bt.isSpecialVar()) {
      dealWithSpec(bt, it, false);
    } else if(it.isSpecialVar()) {
      dealWithSpec(it, bt, true);
    } else if(canBind(bt)) {
      auto binding = _bank.find(bt);

      if(binding) {
        auto b = binding.unwrap();
        if(canCompare(b) && canCompare(it))
        {
          if(!TermSpecOrList::equals(b, it)){
            mismatch=true;
            break;
          }
        } else {
          toDo.push(Constraint(b,it));
        }
      } else {
#if VHOL
        if(env.getMainProblem()->isHigherOrder()) {
          if(it.containsLooseIndex()) {
            mismatch=true;
            break;
          }
        }
#endif
        bind(bt, it);
      }
    } else if (it.isVar() || bt.isVar()) {
      ASS(!canBind(it) && !canBind(bt));
      mismatch=true;
      break;
    } else if (bt.term()->functor() == it.term()->functor()) {
      for (unsigned i = 0; i < bt.term()->arity(); i++) {
        toDo.push(Constraint(bt.nthArg(i), it.nthArg(i)));
      }
    } else {
      mismatch = true;
      break;
    }

    ASS(!mismatch);
  }

  if (mismatch) {
    toDo.reset();
  }

  bdDone();

  if (mismatch) {
    localBD.backtrack();
  } else {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  }

  return !mismatch;
}

/**
 * Unify arguments of @b t1 and @b t2, and return true iff it was successful.
 *
 * @b t1 and @b t2 can be either terms or literals.
 */
template<class T, class V>
bool RobSubstitution<T,V>::unifyArgs(Term* t1, VarBank bank1, Term* t2, VarBank bank2)
{
  ASS_EQ(t1->functor(),t2->functor());
  return unify(TermSpec(TermList(t1), bank1), TermSpec(TermList(t2), bank2));
}


/**
 * Match arguments of @b t1 and @b t2, and return true iff it was successful.
 *
 * @b t1 and @b t2 can be either terms or literals.
 */
template<class T, class V>
bool RobSubstitution<T,V>::matchArgs(Term* base, VarBank baseBank, Term* instance, VarBank instanceBank)
{
  ASS_EQ(base->functor(),instance->functor());

  TermList baseTL(base);
  TermList instanceTL(instance);
  return match(TermSpec(baseTL, baseBank), TermSpec(instanceTL, instanceBank));
}

/**
 * Bind variables from @b denormalizedIndex to variables in @b normalIndex
 * in a way, that applying the substitution to a term in @b denormalizedIndex
 * would give the same result as first renaming variables and then applying
 * the substitution in @b normalIndex.
 *
 * @warning All variables, that occured in some term that was matched or unified
 * in @b normalIndex, must be also present in the @b normalizer.
 */
template<class TermSpecOrList, class VarBankOrInt>
void RobSubstitution<TermSpecOrList, VarBankOrInt>::denormalize(const Renaming& normalizer, VarBankOrInt normalBank, VarBankOrInt denormalizedBank)
{
  VirtualIterator<Renaming::Item> nit=normalizer.items();
  while(nit.hasNext()) {
    Renaming::Item itm=nit.next();
    TermSpecOrList normal(itm.second, normalBank);
    TermSpecOrList denormalized(itm.first, denormalizedBank);

    if (denormalizedBank == _outputIndex) {
      ASS(!_bank.find(normal));
      bind(normal, denormalized);
    } else {
      ASS(!_bank.find(denormalized));
      bind(denormalized,normal);
    }
  }
}

bool RobSubstitution::isUnbound(VarSpec v) const
{
  for(;;) {
    auto binding = _bindings.find(v);
    if(binding.isNone()) {
      return true;
    } else if(binding->isTerm()) {
      return false;
    }
    v = binding->varSpec();
  }
}

/**
 * If special variable @b specialVar is bound to a proper term,
 * return a term, that has the same top functor. Otherwise
 * return an arbitrary variable.
 */
template<class TermSpecOrList, class VarBankOrInt>
TermList::Top RobSubstitution<TermSpecOrList, VarBankOrInt>::getSpecialVarTop(unsigned specialVar) const
{
  TermSpecOrList v(specialVar, VarBank::SPECIAL_BANK);
  for(;;) {
    auto binding = _bank.find(v);
    if (binding.isNone() || binding->isOutputVar()) {
      static TermList auxVarTerm(1,false);
      return auxVarTerm.top();
    } else if(binding->isTerm()) {
      return binding->top();
    }
    v = binding.unwrap();
  }
}

template<class TermSpecOrList, class VarBankOrInt>
Literal* RobSubstitution<TermSpecOrList, VarBankOrInt>::apply(Literal* lit, VarBankOrInt bank) const
{
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit;
  }

  unsigned arity = lit->arity();
  ts.ensure(arity);
  for (unsigned i = 0; i < arity; i++) {
    ts[i]=apply(getLitArg(lit,i,bank),bank);
  }
  if(lit->isTwoVarEquality()){
    TermList sort = apply(getLitSort(lit,bank),bank);
    return Literal::createEquality(lit->polarity(), ts[0], ts[1], sort);
  }

  return Literal::create(lit,ts.array());
}

// AYB do we use this? Not very efficient that we are passing a stack around
// by value
template<class TermSpecOrList, class VarBankOrInt>
Stack<Literal*> RobSubstitution<TermSpecOrList, VarBankOrInt>::apply(Stack<Literal*> cl, VarBankOrInt bank) const
{
  for (unsigned i = 0; i < cl.size(); i++) {
    cl[i] = apply(cl[i], bank);
  }
  return cl;
}

template<class TermSpecOrList, class VarBankOrInt>
size_t RobSubstitution<TermSpecOrList, VarBankOrInt>::getApplicationResultWeight(Literal* lit, VarBankOrInt bank) const
{
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit->weight();
  }

  size_t res = 1; //the predicate symbol weight
  for (unsigned i = 0; i < lit->arity(); i++) {
    size_t argWeight = getApplicationResultWeight(getLitArg(lit,i,bank),bank);
    res += argWeight;
  }
  return res;
}

template<class TermSpecOrList, class VarBankOrInt>
size_t RobSubstitution<TermSpecOrList,VarBankOrInt>::getApplicationResultWeight(TermSpecOrList trm, VarBankOrInt bank) const
{
  return BottomUpEvaluation<AutoDerefTermSpec<TermSpecOrList, VarBankOrInt>, size_t>()
      .function(
          [](auto const& orig, size_t* sizes)
          { return !orig.term.isTerm() ? 1
                                       : (1 + range(0, orig.term.nAllArgs())
                                                  .map([&](auto i) { return sizes[i]; })
                                                  .sum()); })
      .evNonRec([](auto& t) { return someIf(t.term.definitelyGround(),
                                            [&]() -> size_t { return t.term.groundWeight(); }); })
      // .memo<decltype(_applyMemo)&>(_applyMemo)
      .context(AutoDerefTermSpec<TermSpecOrList,VarBankOrInt>::Context(this))
      .apply(AutoDerefTermSpec(TermSpec(trm, bank), this));
}

template<class TermSpecOrList, class VarBankOrInt>
TermList RobSubstitution<TermSpecOrList,VarBankOrInt>::apply(TermSpecOrList trm, VarBankOrInt bank) const
{
  return BottomUpEvaluation<AutoDerefTermSpec<TermSpecOrList,VarBankOrInt>, TermList>()
      .function([&](auto const& orig, TermList* args) -> TermList {
        TermList tout;
        if (orig.term.isVar()) {
          tout = TermList::var(findOrIntroduceOutputVariable(orig.term.varSpec()));

        } else {
          tout = TermList(orig.term.isSort() ? AtomicSort::create(orig.term.functor(), orig.term.nAllArgs(), args)
                                             : Term::create(orig.term.functor(), orig.term.nAllArgs(), args));
        }
        return tout;
      })
      .evNonRec([](auto& t) { return someIf(t.term.definitelyGround(),
                                            [&]() { return t.term.term; }); })
      .memo<decltype(_applyMemo)&>(_applyMemo)
      .context(AutoDerefTermSpec<TermSpecOrList,VarBankOrInt>::Context { .subs = this, })
      .apply(AutoDerefTermSpec(TermSpec(trm, bank), this));
}

/**
 * If @b t is a non-variable, return @b t. Else, if @b t is a variable bound to
 * a non-variable term, return the term. Otherwise, return the root variable
 * to which @b t belongs.
 */
TermSpec const& RobSubstitution::derefBound(TermSpec const& t_) const
{
  TermSpec const* t = &t_;
  for(;;) {
    if (t->isTerm()) {
      return *t;
    } else {
      auto binding = _bindings.find(t->varSpec());
      if (!binding) {
        return *t;
      } else {
        t = &binding.unwrap();
      }
    }
  }
}

template<class T, class H1, class H2>
void RobSubstitution::bind(DHMap<VarSpec, T, H1, H2>& map, const VarSpec& v, T b)
{
  if(bdIsRecording()) {
    ASS(map.find(v).isNone());
    bdAdd(BacktrackObject::fromClosure([this, v, &map](){
      map.remove(v);
      _applyMemo.reset();
    }));
  }
  map.set(v,std::move(b));
  _applyMemo.reset();
}


unsigned RobSubstitution::findOrIntroduceOutputVariable(VarSpec v) const
{
  if (!_startedBindingOutputVars) {
    _startedBindingOutputVars = true;
    ASS_EQ(_nextUnboundAvailable, 0)
    auto& thisMut = const_cast<RobSubstitution&>(*this);
    if (thisMut.bdIsRecording()) {
      thisMut.bdAdd(BacktrackObject::fromClosure([this](){
        _outputVarBindings.reset();
        _nextUnboundAvailable = 0;
        _startedBindingOutputVars = false;
        _applyMemo.reset();
      }));
    }
  }
  ASS(_bindings.find(v).isNone());
  auto found = _outputVarBindings.find(v);
  if (found.isSome()) {
    return *found;
  } else {
    auto newVar = _nextUnboundAvailable++;
    _outputVarBindings.set(v, newVar);
    _applyMemo.reset();
    return newVar;
  }
}

VarSpec RobSubstitution::introGlueVar(TermSpec forTerm)
{

  auto old = _gluedTerms.find(forTerm);
  if (old) {
    return VarSpec(*old, VarBank::GLUE_BANK);
  } else {
    auto v = VarSpec(_nextGlueAvailable++, VarBank::GLUE_BANK);
    _gluedTerms.insert(forTerm, v.var);
    if (bdIsRecording()) {
      bdAdd(BacktrackObject::fromClosure([this, forTerm](){
        _nextGlueAvailable--;
        _gluedTerms.remove(forTerm);
      }));
    }
    bind(v, forTerm);
    return v;
  }
}

void RobSubstitution::bind(const VarSpec& v, TermSpec b)
{
  //Aux terms don't contain special variables, ergo
  //should be shared.
  //ASS(!b.term.isTerm() || b.index!=AUX_INDEX || b.term.term()->shared());
  ASS_NEQ(v.bank, VarBank::UNBOUND_BANK);

  bind(_bindings, v, std::move(b));
}

void RobSubstitution::bindVar(const VarSpec& var, const VarSpec& to)
{
  ASS_NEQ(var,to);

  bind(var,TermSpec(to));
}

bool RobSubstitution::occurs(VarSpec const& toFind, TermSpec const& ts) 
{

   Recycled<DHSet<TermSpec>> encountered;
   Recycled<Stack<TermSpec>> todo;
   todo->push(std::move(ts));

   while (todo->isNonEmpty()){
     auto ts = todo->pop();
     auto dt = derefBound(ts);
     if (!encountered->find(dt)) {
       encountered->insert(dt);
       if (dt.isVar()) {
         if(dt.varSpec() == toFind) {
           return true;
         } else {
           /* nothing to do */
         }
 
       } else {
         todo->loadFromIterator(dt.allArgs());
       }
     }
   }

   return false;
}

bool RobSubstitution::unify(TermSpec s, TermSpec t)
{
#define DEBUG_UNIFY(lvl, ...) if (lvl < 0) DBG("unify: ", __VA_ARGS__)
  DEBUG_UNIFY(0, *this, ".unify(", s, ",", t, ")")


  if(s.sameTermContent(t)) {
    return true;
  }

  BacktrackData localBD;
  bdRecord(localBD);

  static Stack<pair<TermSpec, TermSpec>> toDo(64);
  ASS(toDo.isEmpty());
  toDo.push(make_pair(std::move(s), std::move(t)));

  // Save encountered unification pairs to avoid
  // recomputing their unification
  static DHSet<pair<TermSpec, TermSpec>> encountered_;
  auto encountered = &encountered_;
  encountered->reset();
  

  auto pushTodo = [&](auto pair) {
      // we unify each subterm pair at most once, to avoid worst-case exponential runtimes
      // in order to safe memory we do ot do this for variables.
      // (Note by joe:  didn't make this decision, but just keeping the implemenntation 
      // working as before. i.e. as described in the paper "Comparing Unification 
      // Algorithms in First-Order Theorem Proving", by Krystof and Andrei)
      if (pair.first.isVar() && isUnbound(pair.first.varSpec()) &&
          pair.second.isVar() && isUnbound(pair.second.varSpec())) {
        toDo.push(std::move(pair));
      } else if (!encountered->find(pair)) {
        encountered->insert(pair);
        toDo.push(std::move(pair));
      }
  };

  bool mismatch=false;
  // Iteratively resolve unification pairs in toDo
  // the current pair is always in t1 and t2 with their dereferenced
  // version in dt1 and dt2
  while (toDo.isNonEmpty()) {
    auto x = toDo.pop();
    TermSpec dt1 = derefBound(x.first);
    TermSpec dt2 = derefBound(x.second);
    DEBUG_UNIFY(1, "next pair: ", tie(dt1, dt2))
    // If they have the same content then skip
    // (note that sameTermContent is best-effort)
    if (dt1.sameTermContent(dt2)) {
    // Deal with the case where eithe rare variables
    // Do an occurs-check and note that the variable 
    // cannot be currently bound as we already dereferenced
    } else if(dt1.isVar() && !occurs(dt1.varSpec(), dt2)) {
      bind(dt1.varSpec(), dt2);

    } else if(dt2.isVar() && !occurs(dt2.varSpec(), dt1)) {
      bind(dt2.varSpec(), dt1);

    } else if(dt1.isTerm() && dt2.isTerm() 
           && dt1.functor() == dt2.functor()) {

      for (auto c : dt1.allArgs().zip(dt2.allArgs())) {
        pushTodo(make_pair(std::move(c.first), std::move(c.second)));
      }

    } else {
      mismatch = true;
      break;
    }

    ASS(!mismatch);
  }

  if(mismatch) {
    toDo.reset();
  }

  bdDone();

  if(mismatch) {
    localBD.backtrack();
  } else {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  }

  DEBUG_UNIFY(0, *this)
  return !mismatch;
}

/**
 * Matches @b instance term onto the @b base term.
 * Ordinary variables behave, as one would expect
 * during matching, but special variables aren't
 * being assigned only in the @b base term, but in
 * the instance ass well. (Special variables appear
 * only in internal terms of substitution trees and
 * this behavior allows easy instance retrieval.)
 */
bool RobSubstitution::match(TermSpec base, TermSpec instance)
{
  if(base.sameTermContent(instance)) {
    return true;
  }

  bool mismatch=false;
  BacktrackData localBD;
  bdRecord(localBD);

  static Stack<TermList*> subterms(64);
  ASS(subterms.isEmpty());

  auto obase     = base;
  auto oinstance = instance;
  TermList* bt=&obase.term;
  TermList* it=&oinstance.term;

  TermSpec binding1;
  TermSpec binding2;

  for (;;) {
    TermSpec bts(*bt,base.bank);
    TermSpec its(*it,instance.bank);

    if (!bts.sameTermContent(its) && TermList::sameTopFunctor(bts.term,its.term)) {
      Term* s = bts.term.term();
      Term* t = its.term.term();
      ASS(s->arity() > 0);

      bt = s->args();
      it = t->args();
    } else {
      if (! TermList::sameTopFunctor(bts.term,its.term)) {
	if(bts.term.isSpecialVar()) {
	  VarSpec bvs(bts.term.var(), VarBank::SPECIAL_BANK);
	  auto binding = _bindings.find(bvs);
	  if(binding) {
            binding1 = *binding;
	    ASS_EQ(binding1.bank, base.bank);
	    bt=&binding1.term;
	    continue;
	  } else {
	    bind(bvs,its);
	  }
	} else if(its.term.isSpecialVar()) {
	  VarSpec ivs(its.term.var(), VarBank::SPECIAL_BANK);
	  auto binding = _bindings.find(ivs);
	  if(binding) {
      binding2 = *binding;
	    ASS_EQ(binding2.bank, instance.bank);
	    it=&binding2.term;
	    continue;
	  } else {
	    bind(ivs,bts);
	  }
	} else if(bts.term.isOrdinaryVar()) {
	  VarSpec bvs(bts.term.var(), bts.bank);
	  auto binding = _bindings.find(bvs);
	  if(binding) {
      binding1 = *binding;
	    ASS_EQ(binding1.bank, instance.bank);
	    if(!TermList::equals(binding1.term, its.term))
	    {
	      mismatch=true;
	      break;
	    }
	  } else {
	    bind(bvs,its);
	  }
	} else {
	  mismatch=true;
	  break;
	}
      }

      if (subterms.isEmpty()) {
	break;
      }
      bt = subterms.pop();
      it = subterms.pop();
    }
    if (!bt->next()->isEmpty()) {
      subterms.push(it->next());
      subterms.push(bt->next());
    }
  }

  bdDone();

  subterms.reset();


  if(mismatch) {
    localBD.backtrack();
  } else {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  }

  return !mismatch;
}


Stack<Literal*> RobSubstitution::apply(Stack<Literal*> cl, VarBank bank) const
{
  for (unsigned i = 0; i < cl.size(); i++) {
    cl[i] = apply(cl[i], bank);
  }
  return cl;
}

Literal* RobSubstitution::apply(Literal* lit, VarBank bank) const
{
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit;
  }

  int arity = lit->arity();
  ts.ensure(arity);
  int i = 0;
  for (TermList* args = lit->args(); ! args->isEmpty(); args = args->next()) {
    ts[i++]=apply(*args, bank);
  }
  if(lit->isTwoVarEquality()){
    TermList sort = apply(lit->twoVarEqSort(), bank);
    return Literal::createEquality(lit->polarity(), ts[0], ts[1], sort);
  }

  return Literal::create(lit,ts.array());
}

TermList RobSubstitution::apply(TermList trm, VarBank bank) const
{
  return BottomUpEvaluation<AutoDerefTermSpec, TermList>()
    .function([&](auto const& orig, TermList* args) -> TermList {
        TermList tout;
        if (orig.term.isVar()) {
          tout = TermList::var(findOrIntroduceOutputVariable(orig.term.varSpec()));

        } else {
          tout = TermList(orig.term.isSort() ? AtomicSort::create(orig.term.functor(), orig.term.nAllArgs(), args)
                                             : Term::create(orig.term.functor(), orig.term.nAllArgs(), args));
        }
        return tout;
    })
    .evNonRec([](auto& t) { return someIf(t.term.definitelyGround(), 
                                          [&]() { return t.term.term; }); })
    .memo<decltype(_applyMemo)&>(_applyMemo)
    .context(AutoDerefTermSpec::Context { .subs = this, })
    .apply(AutoDerefTermSpec(TermSpec(trm, bank), this));
}

TermList RobSubstitution::apply(TermSpec t) 
{ return t.toTerm(*this); }

size_t RobSubstitution::getApplicationResultWeight(TermList trm, VarBank bank) const
{
  return BottomUpEvaluation<AutoDerefTermSpec, size_t>()
    .function(
      [](auto const& orig, size_t* sizes) 
      { return !orig.term.isTerm() ? 1 
                                   : (1 + range(0, orig.term.nAllArgs())
                                                      .map([&](auto i) { return sizes[i]; })
                                                      .sum()); })
    .evNonRec([](auto& t) { return someIf(t.term.definitelyGround(), 
                                          [&]() -> size_t { return t.term.groundWeight(); }); })
    // .memo<decltype(_applyMemo)&>(_applyMemo)
    .context(AutoDerefTermSpec::Context { .subs = this, })
    .apply(AutoDerefTermSpec(TermSpec(trm, bank), this))
    ;
}

size_t RobSubstitution::getApplicationResultWeight(Literal* lit, VarBank bank) const
{
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit->weight();
  }

  size_t res = 1; //the predicate symbol weight
  for (TermList* args = lit->args(); ! args->isEmpty(); args = args->next()) {
    size_t argWeight = getApplicationResultWeight(*args, bank);
    res += argWeight;
  }
  return res;
}


/**
 * Return iterator on matching substitutions of @b l1 and @b l2.
 *
 * For guides on use of the iterator, see the documentation of
 * RobSubstitution::AssocIterator.
 */
SubstIterator RobSubstitution::matches(Literal* base, VarBank baseBank, Literal* instance, VarBank instanceBank, bool complementary)
{
  return getAssocIterator<MatchingFn>(this, base, baseBank, instance, instanceBank, complementary);
}

/**
 * Return iterator on unifying substitutions of @b l1 and @b l2.
 *
 * For guides on use of the iterator, see the documentation of
 * RobSubstitution::AssocIterator.
 */
SubstIterator RobSubstitution::unifiers(Literal* l1, VarBank l1Bank, Literal* l2, VarBank l2Bank, bool complementary)
{
  return getAssocIterator<UnificationFn>(this, l1, l1Bank, l2, l2Bank, complementary);
}

template<class Fn>
SubstIterator RobSubstitution::getAssocIterator(RobSubstitution* subst, Literal* l1, VarBank l1Bank, Literal* l2, VarBank l2Bank, bool complementary)
{
  if( !Literal::headersMatch(l1,l2,complementary) ) {
    return SubstIterator::getEmpty();
  }

  if( !l1->commutative() ) {
    return pvi( getContextualIterator(getSingletonIterator(subst),
	    AssocContext<Fn>(l1, l1Bank, l2, l2Bank)) );
  } else {
    return vi(
	    new AssocIterator<Fn>(subst, l1, l1Bank, l2, l2Bank));
  }
}

template<class Fn>
struct RobSubstitution::AssocContext
{
  AssocContext(Literal* l1, VarBank l1Bank, Literal* l2, VarBank l2Bank)
  : _l1(l1), _l1Bank(l1Bank), _l2(l2), _l2Bank(l2Bank)
  {
    ASS(!l1->isEquality());
    ASS(!l2->isEquality());
  } // only used for non-commutative, i.e. also non-equality, literals

  bool enter(RobSubstitution* subst)
  {
    subst->bdRecord(_bdata);
    bool res=Fn::associate(subst, _l1, _l1Bank, _l2, _l2Bank);
    if(!res) {
      subst->bdDone();
      ASS(_bdata.isEmpty());
    }
    return res;
  }
  void leave(RobSubstitution* subst)
  {
    subst->bdDone();
    _bdata.backtrack();
  }
private:
  Literal* _l1;
  VarBank _l1Bank;
  Literal* _l2;
  VarBank _l2Bank;
  BacktrackData _bdata;
};

/**
 * Iterator on associating[1] substitutions of two literals.
 *
 * Using this iterator requires special care, as the
 * substitution being returned is always the same object.
 * The rules for safe use are:
 * - After the iterator is created and before it's
 * destroyed, or hasNext() gives result false, the original
 * substitution is invalid.
 * - Substitution retrieved by call to the method next()
 * is valid only until the hasNext() method is called again
 * (or until the iterator is destroyed).
 * - Before each call to next(), hasNext() has to be called at
 * least once.
 *
 * There rules are quite natural, and the 3rd one is
 * required by many other iterators as well.
 *
 * Template parameter class Fn has to contain following
 * methods:
 * bool associateEqualitySorts(RobSubstitution* subst,
 *  Literal* l1, int l1Index, Literal* l2, int l2Index)
 * bool associate(RobSubstitution*, Literal* l1, int l1Index,
 * 	Literal* l2, int l2Index, bool complementary)
 * bool associate(RobSubstitution*, TermList t1, int t1Index,
 * 	TermList t2, int t2Index)
 *
 * There is supposed to be one Fn class for unification and
 * one for matching.
 *
 * [1] associate means either match or unify
 */
template<class Fn>
class RobSubstitution::AssocIterator: public IteratorCore<RobSubstitution*> {
public:
  AssocIterator(RobSubstitution *subst, Literal *l1, VarBank l1Bank, Literal *l2, VarBank l2Bank)
      : _subst(subst), _l1(l1), _l1Bank(l1Bank), _l2(l2), _l2Bank(l2Bank), _state(FIRST), _used(true)
  {
    ASS_EQ(_l1->functor(), _l2->functor());
    ASS(_l1->commutative());
    ASS_EQ(_l1->arity(), 2);
  }

  ~AssocIterator() override {
    if (_state != FINISHED && _state != FIRST) {
      backtrack(_bdataMain);
      backtrack(_bdataEqAssoc);
    }
    ASS(_bdataMain.isEmpty());
    ASS(_bdataEqAssoc.isEmpty());
  }
  bool hasNext() override {
    if (_state == FINISHED) {
      return false;
    }
    if (!_used) {
      return true;
    }
    _used = false;

    if (_state != FIRST) {
      backtrack(_bdataMain);
    } else {
      _subst->bdRecord(_bdataEqAssoc);
      if (!Fn::associateEqualitySorts(_subst, _l1, _l1Bank, _l2, _l2Bank)) {
        backtrack(_bdataEqAssoc); // this might not be necessary
        _state = FINISHED;
        return false;
      }
    }

    _subst->bdRecord(_bdataMain);

    switch (_state) {
    case NEXT_STRAIGHT:
      if (Fn::associate(_subst, _l1, _l1Bank, _l2, _l2Bank)) {
        _state = NEXT_REVERSED;
        break;
      }
      //no break here intentionally
    case NEXT_REVERSED: {
      TermList t11 = *_l1->nthArgument(0);
      TermList t12 = *_l1->nthArgument(1);
      TermList t21 = *_l2->nthArgument(0);
      TermList t22 = *_l2->nthArgument(1);
      if (Fn::associate(_subst, t11, _l1Bank, t22, _l2Bank)) {
        if (Fn::associate(_subst, t12, _l1Bank, t21, _l2Bank)) {
          _state = NEXT_CLEANUP;
          break;
        }
        //the first successful association will be undone
        //in case NEXT_CLEANUP
      }
    }
      //no break here intentionally
    case NEXT_CLEANUP:
      //undo the previous match
      backtrack(_bdataMain);
      //undo associateEqualitySorts
      backtrack(_bdataEqAssoc);
      _state = FINISHED;
      break;
    case FINISHED:
      ASSERTION_VIOLATION;
    }
    ASS(_state != FINISHED || (_bdataMain.isEmpty() && _bdataEqAssoc.isEmpty()));
    return _state != FINISHED;
  }

  RobSubstitution* next() {
    _used = true;
    return _subst;
  }
private:
  void backtrack(BacktrackData &_bdata) {
    ASS_EQ(&_bdata, &_subst->bdGet());
    _subst->bdDone();
    _bdata.backtrack();
  }

  enum State {
    FIRST = 0,
    NEXT_STRAIGHT = 0,
    NEXT_REVERSED = 1,
    NEXT_CLEANUP = 2,
    FINISHED = 3
  };

  RobSubstitution* _subst;
  Literal* _l1;
  VarBank _l1Bank;
  Literal* _l2;
  VarBank _l2Bank;
  BacktrackData _bdataMain;
  BacktrackData _bdataEqAssoc;

  State _state;
  /**
   * true if the current substitution have already been
   * retrieved by the next() method, or if there isn't
   * any (hasNext() hasn't been called yet)
   */
  bool _used;
};

struct RobSubstitution::MatchingFn {
  static bool associateEqualitySorts(RobSubstitution* subst, Literal* l1, VarBank l1Bank, Literal* l2, VarBank l2Bank) {
    /* Only in the case l1 is of the form X = Y ad l2 is of the form 
       t1 = t2 can the literals be matched without their sorts being matched */
    if(l1->isTwoVarEquality()){
      ASS(l2->isEquality());
      TermList sb = SortHelper::getEqualityArgumentSort(l1);
      TermList si = SortHelper::getEqualityArgumentSort(l2);
      return subst->match(sb, l1Bank, si, l2Bank);
    }
    return true;
  }

  static bool associate(RobSubstitution* subst, Literal* l1, VarBank l1Bank, Literal* l2, VarBank l2Bank)
  { return subst->matchArgs(l1, l1Bank, l2, l2Bank); }

  static bool associate(RobSubstitution* subst, TermList t1, VarBank t1Bank, TermList t2, VarBank t2Bank)
  { return subst->match(t1,t1Bank,t2,t2Bank); }

};

struct RobSubstitution::UnificationFn {

  static bool associateEqualitySorts(RobSubstitution* subst, Literal* l1, VarBank l1Bank, Literal* l2, VarBank l2Bank) {
    if(l1->isEquality()) {
      ASS(l2->isEquality());
      TermList s1 = SortHelper::getEqualityArgumentSort(l1);
      TermList s2 = SortHelper::getEqualityArgumentSort(l2);
      return subst->unify(s1, l1Bank, s2, l2Bank);
    }
    return true;
  }

  static bool associate(RobSubstitution* subst, Literal* l1, VarBank l1Bank, Literal* l2, VarBank l2Bank)
  { return subst->unifyArgs(l1, l1Bank, l2, l2Bank); }

  static bool associate(RobSubstitution* subst, TermList t1, VarBank t1Bank, TermList t2, VarBank t2Bank)
  { return subst->unify(t1, t1Bank, t2, t2Bank); }
};

//std::ostream& operator<<(std::ostream& out, AutoDerefTermSpec const& self)
//{ return out << self.term; }
} // namespace Kernel
