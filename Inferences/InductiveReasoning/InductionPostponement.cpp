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
 * @file InductionPostponement.cpp
 * Implements class InductionPostponement.
 */

// #include <utility>

// #include "Indexing/IndexManager.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "InductionPostponement.hpp"
#include "Inferences/Induction.hpp"

using std::pair;
using std::make_pair;

TermList VAR = TermList(0,false);

namespace Inferences
{

namespace InductiveReasoning
{
using namespace Kernel;
using namespace Lib; 

inline bool isPureCtorTerm(TermList tt) {
  if (tt.isVar()) {
    return false;
  }
  Set<unsigned> vars;
  SubtermIterator sti(tt.term());
  while (sti.hasNext()) {
    auto st = sti.next();
    if (st.isVar()) {
      if (vars.contains(st.var())) {
        // variable has multiple occurrences
        return false;
      }
      vars.insert(st.var());
    } else if (!env.signature->getFunction(st.term()->functor())->termAlgebraCons()) {
      // not term algebra constructor
      return false;
    }
  }
  return true;
}

inline TermList createCtorWithVars(TermAlgebra* ta, unsigned index) {
  auto ctor = ta->constructor(index);
  TermStack args(ctor->arity());
  for (unsigned i = 0; i < ctor->arity(); i++) {
    args.push(TermList(i,false));
  }
  return TermList(Term::create(ctor->functor(), args.size(), args.begin()));
}

void InductionPostponement::attach(SaturationAlgorithm* salg)
{
  CALL("InductionPostponement::attach");

  _salg = salg;
  _enabled = _salg->getOptions().inductionPostponement();
  if (_enabled) {
    _lhsIndex = static_cast<TermIndex*>(salg->getIndexManager()->request(INDUCTION_POSTPONEMENT_LHS_INDEX));
    _literalIndex = static_cast<LiteralIndex*>(salg->getIndexManager()->request(BACKWARD_SUBSUMPTION_SUBST_TREE));
  }
}

void InductionPostponement::detach()
{
  CALL("InductionPostponement::detach");

  if (_enabled) {
    _salg->getIndexManager()->release(BACKWARD_SUBSUMPTION_SUBST_TREE);
    _literalIndex = nullptr;
    _salg->getIndexManager()->release(INDUCTION_POSTPONEMENT_LHS_INDEX);
    _lhsIndex = nullptr;
  }
  _salg = nullptr;
}

/**
 * Postpone the induction formula generation for @b e and the induction
 * application corresponding to @b ctx if needed. If the entry @b e is
 * already postponed, just save the application in the postponed stack
 * of @b e. Otherwise, check if there are clauses that may rewrite or
 * resolve with any literal of the induction formula. This is done by
 * first replacing the placeholder term with a variable @b x in each literal,
 * then finding equations that unify with a subterm of this literal and
 * binds @b x to a term algebra constructor term or finding a literal
 * that unifies with the literal binding @b x in the same way.
 */
bool InductionPostponement::maybePostpone(const InductionContext& ctx, InductionFormulaIndex::Entry* e)
{
  CALL("InductionPostponement::maybePostpone");
  TIME_TRACE("forward induction postponement");
  if (!_enabled) {
    return false;
  }
  // this induction is already postponed
  if (e->_postponed) {
    env.statistics->postponedInductionApplications++;
    e->_postponedApplications.push(ctx);
    return true;
  }
  // if not postponed but this field is initialized,
  // then the induction was reactivated already
  if (e->_activatingClauses.size()) {
    return false;
  }
  TermList sort = SortHelper::getResultSort(ctx._indTerm);
  if (!env.signature->isTermAlgebraSort(sort)) {
    return false;
  }
  auto ta = env.signature->getTermAlgebraOfSort(sort);
  bool postpone = false;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    auto activating = findActivatingClauseForIndex(ctx, i);
    e->_activatingClauses.push(activating);
    if (!activating) {
      postpone = true;
    }
  }
  if (postpone) {
    // update entry and stats
    e->_postponed = true;
    e->_postponedApplications.push(ctx);
    env.statistics->postponedInductions++;
    env.statistics->postponedInductionApplications++;

    // update index
    DHSet<Term*> added;
    auto ph = getPlaceholderForTerm(ctx._indTerm);
    TermReplacement trMaster(ph, VAR);
    auto lIt = ctx.iterLits();
    while (lIt.hasNext()) {
      auto lit = lIt.next();
      Stack<InductionFormulaKey>* ks = nullptr;
      // TODO: This multi-layered indexing is obviously not ideal, update
      // it to a single-layered one once custom LeafData is available
      if (_literalMap.getValuePtr(lit, ks)) {
        auto tlit = trMaster.transform(lit);
        NonVariableNonTypeIterator it(tlit);
        while (it.hasNext()) {
          auto t = it.next();
          if (!t.containsSubterm(VAR) || !added.insert(t.term())) {
            it.right();
            continue;
          }
          _postponedTermIndex.insert(t, tlit, nullptr);
        }
        _postponedLitIndex.insert(tlit, nullptr);
      }
      ASS(ks);
      ks->push(InductionFormulaIndex::represent(ctx));
    }
    return true;
  }
  return false;
}

/**
 * This function checks whether any of the postponed inductions can be
 * finally done by using the currently activated clause @b cl.
 */
void InductionPostponement::checkForPostponedInductions(Literal* lit, Clause* cl, InductionClauseIterator& clIt)
{
  CALL("InductionPostponement::checkForPostponedInductions");
  TIME_TRACE("backward induction postponement");
  if (!_enabled) {
    return;
  }
  ASS(_toBeRemoved.isEmpty());

  if (lit->isEquality()) {
    if (lit->isPositive()) {
      for (unsigned j=0; j<2; j++) {
        auto lhs = *lit->nthArgument(j);
        auto qrit = _postponedTermIndex.getUnifications(lhs,true);
        while (qrit.hasNext()) {
          auto qr = qrit.next();
          auto tt = qr.substitution->applyToResult(VAR);
          // prefilter: if term is not ctor term, skip
          if (!isPureCtorTerm(tt)) {
            continue;
          }
          performInductionsIfNeeded(tt, qr.literal, cl, clIt);
        }
      }
    }
  } else {
    auto qrit = _postponedLitIndex.getUnifications(lit, true/*complementary*/, true);
    while (qrit.hasNext()) {
      auto qr = qrit.next();
      auto tt = qr.substitution->applyToResult(VAR);
      // prefilter: if term is not ctor term, skip
      if (!isPureCtorTerm(tt)) {
        continue;
      }
      performInductionsIfNeeded(tt, qr.literal, cl, clIt);
    }
  }
  // The removal of inductions that were done above must be performed
  // afterwards, since we were traversing the indices until this point
  decltype(_toBeRemoved)::Iterator rit(_toBeRemoved);
  while (rit.hasNext()) {
    Literal* lit = rit.next();
    _literalMap.remove(lit);
    DHSet<Term*> removed;
    _postponedLitIndex.remove(lit, nullptr);
    NonVariableNonTypeIterator it(lit);
    while (it.hasNext()) {
      auto t = it.next();
      if (!t.containsSubterm(VAR) || !removed.insert(t.term())) {
        it.right();
        continue;
      }
      _postponedTermIndex.remove(t, lit, nullptr);
    }
  }
  _toBeRemoved.reset();
}

void InductionPostponement::performInductionsIfNeeded(TermList t, Literal* lit, Clause* cl, InductionClauseIterator& clIt)
{
  CALL("InductionPostponement::performInductionsIfNeeded");
  if (!t.isTerm()) {
    return;
  }
  if (_toBeRemoved.contains(lit)) {
    return;
  }
  TermList sort = SortHelper::getResultSort(t.term());
  if (!env.signature->isTermAlgebraSort(sort)) {
    return;
  }
  auto ta = env.signature->getTermAlgebraOfSort(sort);
  Substitution subst;
  subst.bind(VAR.var(), getPlaceholderForTerm(t.term()));
  auto ks = _literalMap.findPtr(lit->apply(subst));

  // intentionally not incrementing i here
  for (unsigned i = 0; i < ks->size();) {
    auto e = _formulaIndex.findByKey((*ks)[i]);
    ASS(e);
    ASS(e->_postponed);
    ASS(e->_postponedApplications.isNonEmpty());

    ASS_EQ(e->_activatingClauses.size(), ta->nConstructors());
    bool activate = true;
    for (unsigned j = 0; j < ta->nConstructors(); j++) {
      auto& acl = e->_activatingClauses[j];
      if (acl && acl->store() == Clause::NONE) {
        acl = findActivatingClauseForIndex(e->_postponedApplications[0], j);
      }
      if (!acl) {
        if (ta->constructor(j)->functor() == t.term()->functor()) {
          acl = cl;
        } else {
          activate = false;
        }
      }
    }
    if (!activate) {
      i++;
      continue;
    }
    // any of the postponed contexts suffices to generate the formulas
    clIt.generateStructuralFormulas(e->_postponedApplications[0], e);
    ASS_NEQ(0,env.statistics->postponedInductions);
    env.statistics->postponedInductions--;
    while (e->_postponedApplications.isNonEmpty()) {
      auto ctx = e->_postponedApplications.pop();
      ASS_NEQ(0,env.statistics->postponedInductionApplications);
      env.statistics->postponedInductionApplications--;

      for (auto& kv : e->get()) {
        clIt.resolveClauses(kv.first, ctx, kv.second);
      }
    }
    e->_postponed = false;
    // remove the entry from the literal
    swap((*ks)[i],ks->top());
    ks->pop();
  }
  if (ks->isEmpty()) {
    _toBeRemoved.insert(lit);
  }
}

Clause* InductionPostponement::findActivatingClauseForIndex(const InductionContext& ctx, unsigned index)
{
  CALL("InductionPostponement::findActivatingClauseForIndex");
  TermList sort = SortHelper::getResultSort(ctx._indTerm);
  ASS(env.signature->isTermAlgebraSort(sort));
  auto ta = env.signature->getTermAlgebraOfSort(sort);
  auto ph = getPlaceholderForTerm(ctx._indTerm);
  TermReplacement trMaster(ph, VAR);
  RobSubstitution subst;
  DHSet<Term*> tried;

  // create ctor replacement
  Substitution ctorSubst;
  ctorSubst.bind(VAR.var(), createCtorWithVars(ta, index));

  // check if there is a literal which unifies with an equality or
  // an opposite sign literal, if not store subterms in an index
  Clause* activating = nullptr;
  auto lIt = ctx.iterLits();
  while (!activating && lIt.hasNext()) {
    auto litMaster = trMaster.transform(lIt.next());

    NonVariableNonTypeIterator nvi(litMaster);
    while (!activating && nvi.hasNext()) {
      auto master = nvi.next();
      if (!master.containsSubterm(VAR)) {
        nvi.right();
        continue;
      }
      auto ctor = SubstHelper::apply(master, ctorSubst);
      if (!tried.insert(ctor.term())) {
        nvi.right();
        continue;
      }

      auto uit = _lhsIndex->getUnifications(ctor, false);
      while (uit.hasNext()) {
        auto qr = uit.next();
        subst.reset();
        ALWAYS(subst.unify(master, 0, qr.term, 1));
        auto tt = subst.apply(VAR, 0);
        if (isPureCtorTerm(tt)) {
          activating = qr.clause;
          break;
        }
      }
    }
    if (!activating && !litMaster->isEquality()) {
      auto litCtor = SubstHelper::apply(litMaster, ctorSubst);
      auto uit = _literalIndex->getUnifications(litCtor, true/*complementary*/, false);
      while (uit.hasNext()) {
        auto qr = uit.next();
        subst.reset();
        ALWAYS(subst.unifyArgs(litMaster, 0, qr.literal, 1));
        auto tt = subst.apply(VAR, 0);
        if (isPureCtorTerm(tt)) {
          activating = qr.clause;
          break;
        }
      }
    }
  }
  return activating;
}

}

}
