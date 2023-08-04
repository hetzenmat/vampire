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

#include "Demodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

// common code

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

void ForwardDemodulationNew::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );

  _preorderedOnly = getOptions().forwardDemodulation()== Options::Demodulation::PREORDERED;
  _redundancyCheck = getOptions().demodulationRedundancyCheck() != Options::DemodulationRedunancyCheck::OFF;
  _encompassing = getOptions().demodulationRedundancyCheck() == Options::DemodulationRedunancyCheck::ENCOMPASS;
}

void ForwardDemodulationNew::detach()
{
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardSimplificationEngine::detach();
}

template <bool combinatorySupSupport>
VirtualIterator<pair<Clause*,ClauseIterator>> ForwardDemodulationImplNew<combinatorySupSupport>::perform(Clause* cl)
{
  TIME_TRACE("forward demodulation");

  //Perhaps it might be a good idea to try to
  //replace subterms in some special order, like
  //the heaviest first...

  _normalForms.reset();

  auto clen = cl->length();
  auto lits = LiteralStack::fromIterator(cl->iterLits());
  bool eqTaut = false;
  Clause* premise = nullptr;
  ClauseStack premises;

  while (forwardSimplifyingLoop(lits, eqTaut, premise)) {
    ASS(premise);
    premises.push(premise);
    if (eqTaut) {
      break;
    }
  }

  if (eqTaut) {
    env.statistics->forwardDemodulationsToEqTaut++;
    return pvi(getSingletonIterator(make_pair((Clause*)nullptr,getUniquePersistentIterator(ClauseStack::Iterator(premises)))));
  }

  if (premises.isNonEmpty()) {
    auto premLst = UnitList::singleton(cl);
    for (const auto& cl : premises) {
      UnitList::push(cl, premLst);
    }
    Clause* res = new(clen) Clause(clen, SimplifyingInferenceMany(InferenceRule::FORWARD_DEMODULATION,premLst));
    
    for (unsigned i = 0; i < clen; i++) {
      (*res)[i]=lits[i];
    }

    env.statistics->forwardDemodulations++;
    return pvi(getSingletonIterator(make_pair(res,getUniquePersistentIterator(ClauseStack::Iterator(premises)))));
  }

  // return false;
  return VirtualIterator<pair<Clause*,ClauseIterator>>::getEmpty();
}

// This is necessary for templates defined in cpp files.
// We are happy to do it for ForwardDemodulationImplNew, since it (at the moment) has only two specializations:
template class ForwardDemodulationImplNew<false>;
template class ForwardDemodulationImplNew<true>;

template<bool combinatorySupSupport>
bool ForwardDemodulationImplNew<combinatorySupSupport>::forwardSimplifyingLoop(LiteralStack& lits, bool eqTaut, Clause*& premise)
{
  TermList noNormalForm;
  noNormalForm.makeEmpty();
  TIME_TRACE("forward demodulation inner");

  const auto& ord = _salg->getOrdering();
  Term* topLevelCheckTerm = nullptr;
  if (lits.size() == 1 && lits[0]->isEquality() && lits[0]->isPositive()) {
    TIME_TRACE("positive unit argument order");
    Ordering::Result litOrder = ord.getEqualityArgumentOrder(lits[0]);
    auto t1 = lits[0]->termArg(0);
    auto t2 = lits[0]->termArg(1);
    if (litOrder == Ordering::LESS) {
      ASS(t2.isTerm());
      topLevelCheckTerm = t2.term();
    } else if (litOrder == Ordering::GREATER) {
      ASS(t1.isTerm());
      topLevelCheckTerm = t1.term();
    }
  }

  for(auto& lit : lits) {
    typename std::conditional<!combinatorySupSupport,
      NonVariableNonTypeIterator,
      FirstOrderSubtermIt>::type it(lit);
    while(it.hasNext()) {
      TypedTermList trm = it.next();
      TIME_TRACE("trm");
      auto ptr = _normalForms.findPtr(trm.term());
      if (ptr) {
        TIME_TRACE("done");
        auto nf = ptr->first;
        auto isRenaming = ptr->second;
        if (nf.isEmpty()) {
          it.right();
          continue;
        }
        TIME_TRACE("nf");

        if (trm.term() == topLevelCheckTerm && isRenaming) {
          TermList other = EqHelper::getOtherEqualitySide(lit, trm);
          Ordering::Result tord = ord.compare(nf, other);
          if (tord == Ordering::LESS || tord == Ordering::LESS_EQ) {
            lit = EqHelper::replace(lit,trm,nf);
            // premise = qr.clause;
            eqTaut = EqHelper::isEqTautology(lit);
            return true;
          }
        } else {
          lit = EqHelper::replace(lit,trm,nf);
          // premise = qr.clause;
          eqTaut = EqHelper::isEqTautology(lit);
          return true;
        }
      }

      TIME_TRACE("indexing");
      TermQueryResultIterator git = _index->getGeneralizations(trm, true);
      while(git.hasNext()) {
        TermQueryResult qr=git.next();
        ASS_EQ(qr.clause->length(),1);

        // to deal with polymorphic matching
        // Ideally, we would like to extend the substitution
        // returned by the index to carry out the sort match.
        // However, ForwardDemodulation uses a CodeTree as its
        // indexing mechanism, and it is not clear how to extend
        // the substitution returned by a code tree.
        static RobSubstitution subst;
        bool resultTermIsVar = qr.term.isVar();
        TIME_TRACE("1");
        if(resultTermIsVar){
          TermList querySort = trm.sort();
          TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
          subst.reset();
          if(!subst.match(eqSort, 0, querySort, 1)){
            continue;
          }
        }

        TIME_TRACE("2");
        TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
        TermList rhsS=getRhsInstance(qr.substitution.ptr(),trm,qr.term,rhs,true/*eqIsResult*/);
        if(resultTermIsVar){
          rhsS = subst.apply(rhsS, 0);
        }

        TIME_TRACE("3");
        Ordering::Result argOrder = ord.getEqualityArgumentOrder(qr.literal);
        bool preordered = argOrder==Ordering::LESS || argOrder==Ordering::GREATER;
        if (!preordered && ord.compare(trm,rhsS) != Ordering::GREATER) {
          continue;
        }

        TIME_TRACE("4");
        auto isRenaming = qr.substitution->isRenamingOn(qr.term,true/*eqIsResult*/);

        if (trm.term() == topLevelCheckTerm && isRenaming) {
          TermList other = EqHelper::getOtherEqualitySide(lit, trm);
          Ordering::Result tord = ord.compare(rhsS, other);
          if (tord != Ordering::LESS && tord != Ordering::LESS_EQ) {
            continue;
          }
        }

        TIME_TRACE("5");
        lit = EqHelper::replace(lit,trm,rhsS);
        premise = qr.clause;
        eqTaut = EqHelper::isEqTautology(lit);
        _normalForms.insert(trm.term(),make_pair(rhsS,isRenaming));
        return true;
      }
      _normalForms.insert(trm.term(),make_pair(noNormalForm,false));
    }
  }
  return false;
}

}