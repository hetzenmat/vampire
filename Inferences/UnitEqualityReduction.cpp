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
 * @file Demodulation.cpp
 * Implements class Demodulation.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/Timer.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "UnitEqualityReduction.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

inline TermList getRhsInstance(ResultSubstitution* subst, TermList trm, TermList lhs, TermList rhs, bool eqIsResult)
{
  TermList rhsS;
  if (eqIsResult && subst->isIdentityOnQueryWhenResultBound()) {
    return subst->applyToBoundResult(rhs);
  }
  if (!eqIsResult && subst->isIdentityOnResultWhenQueryBound()) {
    return subst->applyToBoundQuery(rhs);
  }

  //When we apply substitution to the rhs, we get a term, that is
  //a variant of the term we'd like to get, as new variables are
  //produced in the substitution application.
  TermList lhsSBadVars = subst->apply(lhs,eqIsResult);
  TermList rhsSBadVars = subst->apply(rhs,eqIsResult);
  Renaming rNorm, qNorm, qDenorm;
  rNorm.normalizeVariables(lhsSBadVars);
  qNorm.normalizeVariables(trm);
  qDenorm.makeInverse(qNorm);
  ASS_EQ(trm,qDenorm.apply(rNorm.apply(lhsSBadVars)));
  return qDenorm.apply(rNorm.apply(rhsSBadVars));
}

void forwardSimplify(TermList& t, DemodulationLHSIndex* index, const Ordering& ord)
{
  TIME_TRACE("unit equality reduction forward simplify");

  while (true) {
    NonVariableNonTypeIterator nvi(t.term());
    bool reduced = false;
    while(nvi.hasNext()) {
      TypedTermList trm = nvi.next();
      TermQueryResultIterator git = index->getGeneralizations(trm, true);
      while(git.hasNext()) {
        TermQueryResult qr=git.next();
        TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
        TermList rhsS=getRhsInstance(qr.substitution.ptr(),trm,qr.term,rhs,true/*eqIsResult*/);

        Ordering::Result argOrder = ord.getEqualityArgumentOrder(qr.literal);
        bool preordered = argOrder==Ordering::LESS || argOrder==Ordering::GREATER;
        if (!preordered && ord.compare(trm,rhsS) != Ordering::GREATER) {
          continue;
        }
        t = TermList(EqHelper::replace(t.term(),trm,rhsS));
        reduced = true;
        break;
      }
      if (reduced) {
        break;
      }
    }
    if (!reduced) {
      break;
    }
  }
}

// we have a ground critical pair s[r] = t from the ground overlap s[r] <- s[l] -> t
// where t is from the ground conjecture conj : u[t] != w and
// cpMain : s[l] = t and cpSide : l = r are unit equations
// we simplify u[t] != w into u[s[r]] != w if s[r] < t 
Clause* UnitEqualityReduction::perform(Clause* conj, Literal* conjLit, Clause* cpMain, Literal* cpMainLit, Clause* cpSide, Literal* cpSideLit, TermList l, TermList t, const Ordering& ord, DemodulationLHSIndex* index)
{
  TermList r = EqHelper::getOtherEqualitySide(cpSideLit,l);
  TermList sl = EqHelper::getOtherEqualitySide(cpMainLit,t);
  TermList sr(EqHelper::replace(sl.term(), l, r));
  forwardSimplify(sr, index, ord);
  if (ord.compare(t,sr) != Ordering::Result::GREATER) {
    return nullptr;
  }

  Literal* resLit = EqHelper::replace(conjLit,t,sr);

  UnitList* premList = UnitList::cons(conj, UnitList::cons(cpMain, UnitList::singleton(cpSide)));

  Clause* res = new(1) Clause(1, SimplifyingInferenceMany(InferenceRule::UNIT_EQUALITY_REDUCTION, premList));
  (*res)[0]=resLit;
  env.statistics->unitEqualityReductions++;
  // cout << "simplified " << *cl << endl
  //      << "premise 1  " << *qr1.clause << endl
  //      << "premise 2  " << *qr2.clause << endl
  //      << "result     " << *res << endl << endl;
  return res;
}

void ForwardUnitEqualityReduction::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
  _lhsIndex=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
  _rhsIndex=static_cast<RewritingRHSIndex*>(
	  _salg->getIndexManager()->request(UNIT_REWRITING_RHS_INDEX) );
}

void ForwardUnitEqualityReduction::detach()
{
  _lhsIndex=0;
  _rhsIndex=0;
  _salg->getIndexManager()->release(UNIT_REWRITING_RHS_INDEX);
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardSimplificationEngine::detach();
}

VirtualIterator<pair<Clause*,ClauseIterator>> ForwardUnitEqualityReduction::perform(Clause* cl)
{
  if (cl->length()!=1 || !cl->isGround()) {
    return VirtualIterator<pair<Clause*,ClauseIterator>>::getEmpty();
  }

  auto lit = (*cl)[0];

  if (!lit->isEquality() || lit->isPositive()) {
    return VirtualIterator<pair<Clause*,ClauseIterator>>::getEmpty();
  }

  return pvi(iterTraits(getUniquePersistentIterator(vi(new NonVariableNonTypeIterator(lit))))
    .flatMap([this](Term* t) {
      return pvi(pushPairIntoRightIterator(t, _rhsIndex->getGeneralizations(t, true)));
    })
    .flatMap([](pair<Term*,TermQueryResult> arg) {
      auto qr = arg.second;
      auto eqLitS = qr.substitution->applyToBoundResult(qr.literal);
      auto otherSide = EqHelper::getOtherEqualitySide(eqLitS,TermList(arg.first));
      return pvi(pushPairIntoRightIterator(arg, getUniquePersistentIterator(vi(new NonVariableNonTypeIterator(otherSide.term())))));
    })
    .flatMap([this](pair<pair<Term*,TermQueryResult>,Term*> arg) {
      return pvi(pushPairIntoRightIterator(arg, _lhsIndex->getGeneralizations(arg.second, true)));
    })
    .map([this,lit,cl](pair<pair<pair<Term*,TermQueryResult>,Term*>,TermQueryResult> arg) -> pair<Clause*,ClauseIterator> {
      const auto& ord = _salg->getOrdering();
      auto t = arg.first.first.first;
      auto qr1 = arg.first.first.second;
      auto overlap = arg.first.second;
      auto qr2 = arg.second;

      auto res = UnitEqualityReduction::perform(
        cl, lit,
        qr1.clause, qr1.substitution->applyToBoundResult(qr1.literal),
        qr2.clause, qr2.substitution->applyToBoundResult(qr2.literal),
        TermList(overlap), TermList(t), ord, _lhsIndex);
      return make_pair(res,pvi(getSingletonIterator(qr1.clause)));
    })
    .filter([](pair<Clause*,ClauseIterator> arg) {
      return arg.first;
    })
    .timeTraced("forward unit equality reduction"));
}


void BackwardUnitEqualityReduction::attach(SaturationAlgorithm* salg)
{
  BackwardSimplificationEngine::attach(salg);
  _index=static_cast<UnitEqualityConjectureIndex*>(
	  _salg->getIndexManager()->request(UNIT_EQUALITY_CONJECTURE_INDEX) );
  _lhsIndex=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
  _overlapIndex=static_cast<SuperpositionSubtermIndex*>(
	  _salg->getIndexManager()->request(SUPERPOSITION_SUBTERM_SUBST_TREE) );
}

void BackwardUnitEqualityReduction::detach()
{
  _index=0;
  _lhsIndex=0;
  _overlapIndex=0;
  _salg->getIndexManager()->release(SUPERPOSITION_SUBTERM_SUBST_TREE);
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  _salg->getIndexManager()->release(UNIT_EQUALITY_CONJECTURE_INDEX);
  BackwardSimplificationEngine::detach();
}

void BackwardUnitEqualityReduction::perform(Clause* cl, BwSimplificationRecordIterator& simplifications)
{
  TIME_TRACE("backward unit equality reduction");

  if(cl->length()!=1 || !(*cl)[0]->isEquality() || !(*cl)[0]->isPositive() ) {
    simplifications=BwSimplificationRecordIterator::getEmpty();
    return;
  }
  Literal* lit=(*cl)[0];
  DHSet<Clause*> simplified;

  auto it1 = iterTraits(EqHelper::getDemodulationLHSIterator(lit, false, _salg->getOrdering(), _salg->getOptions()))
    .filter([lit](TermList t) {
      auto other = EqHelper::getOtherEqualitySide(lit, t);
      return other.containsAllVariablesOf(t);
    })
    .map([lit](TermList t) {
      return EqHelper::getOtherEqualitySide(lit, t);
    })
    .flatMap([this,lit](TermList t) {
      return pvi(pushPairIntoRightIterator(t, _index->getInstances(TypedTermList(t,SortHelper::getEqualityArgumentSort(lit)))));
    })
    .filter([&simplified](pair<TermList,TermQueryResult> arg) {
      auto cl = arg.second.clause;
      return !simplified.find(cl) && cl->length()==1 && (*cl)[0]->isNegative() && (*cl)[0]->isEquality() /* && (*cl)[0]->ground() */;
    })
    .flatMap([lit](pair<TermList,TermQueryResult> arg) {
      auto qr = arg.second;
      auto eqLitS = qr.substitution->applyToBoundQuery(lit);
      auto otherSide = EqHelper::getOtherEqualitySide(eqLitS,qr.term);
      return pvi(pushPairIntoRightIterator(arg, getUniquePersistentIterator(vi(new NonVariableNonTypeIterator(otherSide.term())))));
    })
    .flatMap([this](pair<pair<TermList,TermQueryResult>,Term*> arg) {
      return pvi(pushPairIntoRightIterator(arg, _lhsIndex->getGeneralizations(arg.second, true)));
    })
    .map([this,lit,cl,&simplified](pair<pair<pair<TermList,TermQueryResult>,Term*>,TermQueryResult> arg) -> BwSimplificationRecord {
      const auto& ord = _salg->getOrdering();
      auto qr1 = arg.first.first.second;
      auto overlap = arg.first.second;
      auto qr2 = arg.second;

      auto res = UnitEqualityReduction::perform(
        qr1.clause, qr1.literal,
        cl, qr1.substitution->applyToBoundQuery(lit),
        qr2.clause, qr2.substitution->applyToBoundResult(qr2.literal),
        TermList(overlap), qr1.term, ord, _lhsIndex);
      if (!res) {
        return BwSimplificationRecord(0);
      }
      simplified.insert(qr1.clause);
      return BwSimplificationRecord(qr1.clause,res);
    })
    .filter([](BwSimplificationRecord arg) {
      return arg.toRemove;
    })
    .timeTraced("backward unit equality reduction 1")
    .persistent(); // otherwise we might remove things from the
                   // DemodulationSubtermIndex while traversing it


  // auto it2 = iterTraits(EqHelper::getDemodulationLHSIterator(lit, false, _salg->getOrdering(), _salg->getOptions()))
  //   .flatMap([this,lit](TermList t) {
  //     return pvi(pushPairIntoRightIterator(t, _overlapIndex->getUnifications(TypedTermList(t,SortHelper::getEqualityArgumentSort(lit)))));
  //   })
  //   .timeTraced("1")
  //   .filter([](pair<TermList,TermQueryResult> arg) {
  //     auto lit = arg.second.literal;
  //     if (lit->isNegative() || !lit->isEquality()) {
  //       return false;
  //     }
  //     auto l0 = lit->termArg(0);
  //     auto l1 = lit->termArg(1);
  //     return l0.containsAllVariablesOf(l1) && l1.containsAllVariablesOf(l0);
  //   })
  //   .timeTraced("2")
  //   .flatMap([this](pair<TermList,TermQueryResult> arg) {
  //     return pvi(pushPairIntoRightIterator(arg, EqHelper::getLHSIterator(arg.second.literal, _salg->getOrdering())));
  //   })
  //   .filter([](pair<pair<TermList,TermQueryResult>,TermList> arg) {
  //     return arg.second.containsSubterm(arg.first.second.term);
  //   })
  //   .timeTraced("3")
  //   .flatMap([this](pair<pair<TermList,TermQueryResult>,TermList> arg) {
  //     auto lit = arg.first.second.literal;
  //     auto other = EqHelper::getOtherEqualitySide(lit, arg.second);
  //     TermList otherS;
  //     {
  //       TIME_TRACE("apply unifier");
  //       otherS = arg.first.second.substitution->apply(other, true);
  //     }
  //     return pvi(pushPairIntoRightIterator(arg.first, _index->getInstances(TypedTermList(otherS,SortHelper::getEqualityArgumentSort(lit)))));
  //   })
  //   .timeTraced("4")
  //   .filter([&simplified](pair<pair<TermList,TermQueryResult>,TermQueryResult> arg) {
  //     auto cl = arg.second.clause;
  //     return !simplified.find(cl) && cl->length()==1 && (*cl)[0]->isNegative() && (*cl)[0]->isEquality();
  //   })
  //   .timeTraced("5")
  //   .map([this,lit,cl,&simplified](pair<pair<TermList,TermQueryResult>,TermQueryResult> arg) -> BwSimplificationRecord {
  //     const auto& ord = _salg->getOrdering();
  //     auto qrConj = arg.second;
  //     auto qrCpMain = arg.first.second;
  //     auto overlap = qrConj.substitution->applyToBoundQuery(qrCpMain.substitution->apply(arg.first.first, false));

  //     auto res = UnitEqualityReduction::perform(
  //       qrConj.clause, qrConj.literal,
  //       qrCpMain.clause, qrConj.substitution->applyToBoundQuery(qrCpMain.substitution->apply(qrCpMain.literal, true)),
  //       cl, qrConj.substitution->applyToBoundQuery(qrCpMain.substitution->apply(lit, false)),
  //       overlap, qrConj.term, ord);
  //     if (!res) {
  //       return BwSimplificationRecord(0);
  //     }
  //     simplified.insert(qrConj.clause);
  //     return BwSimplificationRecord(qrConj.clause,res);
  //   })
  //   .timeTraced("6")
  //   .filter([](BwSimplificationRecord arg) {
  //     return arg.toRemove;
  //   })
  //   .timeTraced("backward unit equality reduction 2")
  //   .persistent(); // otherwise we might remove things from the
  //                  // DemodulationSubtermIndex while traversing it

  // simplifications = pvi(getConcatenatedIterator(it1,it2));
  simplifications = pvi(it1);
}

}