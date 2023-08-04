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

      auto eqLitS = qr1.substitution->applyToBoundResult(qr1.literal);
      auto overlapOtherSide = EqHelper::getOtherEqualitySide(qr2.substitution->applyToBoundResult(qr2.literal),TermList(overlap));
      auto finalTerm = EqHelper::replace(EqHelper::getOtherEqualitySide(eqLitS,TermList(t)).term(),TermList(overlap),overlapOtherSide);
      if (ord.compare(TermList(t),TermList(finalTerm)) != Ordering::Result::GREATER) {
        return make_pair(nullptr,ClauseIterator::getEmpty());
      }

      auto resLit = EqHelper::replace(lit,TermList(t),TermList(finalTerm));

      UnitList* premList = UnitList::cons(cl, UnitList::cons(qr1.clause, UnitList::singleton(qr2.clause)));

      Clause* res = new(1) Clause(1,
        SimplifyingInferenceMany(InferenceRule::UNIT_EQUALITY_REDUCTION, premList));
      (*res)[0]=resLit;
      env.statistics->unitEqualityReductions++;
      // cout << "simplified " << *cl << endl
      //      << "premise 1  " << *qr1.clause << endl
      //      << "premise 2  " << *qr2.clause << endl
      //      << "result     " << *res << endl << endl;
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
  _index=static_cast<DemodulationSubtermIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE) );
  _lhsIndex=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
}

void BackwardUnitEqualityReduction::detach()
{
  _index=0;
  _lhsIndex=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
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

  simplifications = pvi(iterTraits(EqHelper::getDemodulationLHSIterator(lit, false, _salg->getOrdering(), _salg->getOptions()))
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
      return !simplified.find(cl) && cl->length()==1 && (*cl)[0]->isNegative() && (*cl)[0]->isEquality();
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

      auto eqLitS = qr1.substitution->applyToBoundQuery(lit);
      auto overlapOtherSide = EqHelper::getOtherEqualitySide(qr2.substitution->applyToBoundResult(qr2.literal),TermList(overlap));
      auto finalTerm = EqHelper::replace(EqHelper::getOtherEqualitySide(eqLitS,qr1.term).term(),TermList(overlap),overlapOtherSide);

      if (ord.compare(qr1.term,TermList(finalTerm)) != Ordering::Result::GREATER) {
        return BwSimplificationRecord(nullptr);
      }

      auto resLit = EqHelper::replace(qr1.literal,qr1.term,TermList(finalTerm));

      UnitList* premList = UnitList::cons(cl, UnitList::cons(qr1.clause, UnitList::singleton(qr2.clause)));

      Clause* res = new(1) Clause(1,
        SimplifyingInferenceMany(InferenceRule::UNIT_EQUALITY_REDUCTION, premList));
      (*res)[0]=resLit;
      env.statistics->unitEqualityReductions++;
      cout << "simplified " << *qr1.clause << endl
           << "premise 1  " << *cl << endl
           << "premise 2  " << *qr2.clause << endl
           << "result     " << *res << endl << endl;
      simplified.insert(qr1.clause);
      return BwSimplificationRecord(qr1.clause,res);
    })
    .filter([](BwSimplificationRecord arg) {
      return arg.toRemove;
    })
    .persistent()); // otherwise we might remove things from the
                    // DemodulationSubtermIndex while traversing it
}

}