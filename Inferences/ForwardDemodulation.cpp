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
 * @file ForwardDemodulation.cpp
 * Implements class ForwardDemodulation.
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
#include "Kernel/Matcher.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Indexing/CodeTreeInterfaces.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "ForwardDemodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void ForwardDemodulation::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
  _bwIndex=static_cast<DemodulationSubtermIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE) );

  _preorderedOnly = getOptions().forwardDemodulation()== Options::Demodulation::PREORDERED;
  _redundancyCheck = getOptions().demodulationRedundancyCheck() != Options::DemodulationRedunancyCheck::OFF;
  _encompassing = getOptions().demodulationRedundancyCheck() == Options::DemodulationRedunancyCheck::ENCOMPASS;
}

void ForwardDemodulation::detach()
{
  _bwIndex = nullptr;
  _index=0;
  _bwIndex=0;
  _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardSimplificationEngine::detach();
}

Term* NonParallelNonVariableNonTypeIterator::next()
{
  Term* t = _stack.pop();
  TermList* ts;
  _added = 0;  
  Signature::Symbol* sym;
  if (t->isLiteral()) {
    sym = env.signature->getPredicate(t->functor());
  } else{
    sym = env.signature->getFunction(t->functor());
  }
  unsigned taArity; 
  unsigned arity;

  if(t->isLiteral() && static_cast<Literal*>(t)->isEquality()){
    taArity = 0;
    arity = 2;
  } else {
    taArity = sym->numTypeArguments();
    arity = sym->arity();
  }

  for(unsigned i = taArity; i < arity; i++){
    ts = t->nthArgument(i);
    if (ts->isTerm()) {
      _stack.push(const_cast<Term*>(ts->term()));
      _added++;
    }
  }
  return t;
}

void NonParallelNonVariableNonTypeIterator::right()
{
  while (_added > 0) {
    _added--;
    _stack.pop();
  }
}


void handleSubtermsForBackwardDemodulation(Clause* cl, Term* t, DemodulationSubtermIndex* index)
{
  TIME_TRACE("extra insertion");
  // cout << "insert " << *t << endl << "from " << *cl << endl;
  cl->incRefCnt();
  ASS_EQ(cl->length(),1);
  auto lit = (*cl)[0];
  DHSet<Term*> done;
  NonVariableNonTypeIterator nvi(lit);
  while (nvi.hasNext()) {
    auto st = nvi.next();
    if (!done.insert(st) || !st->containsSubterm(TermList(t))) {
      nvi.right();
      continue;
    }
    TIME_TRACE("insert term into bw index");
    index->getIS()->insert(st, lit, cl);
  }
  nvi.reset(t);
  while (nvi.hasNext()) {
    auto st = nvi.next();
    if (!done.insert(st)) {
      nvi.right();
      continue;
    }
    TIME_TRACE("insert term into bw index");
    index->getIS()->insert(st, lit, cl);
  }
}

template <bool combinatorySupSupport>
VirtualIterator<pair<Clause*,ClauseIterator>> ForwardDemodulationImpl<combinatorySupSupport>::perform(Clause* cl)
{
  TIME_TRACE("forward demodulation");
  TimeTrace::ScopedTimer timer("forward demodulation time until first match");

  auto resIt = VirtualIterator<pair<Clause*,ClauseIterator>>::getEmpty();
  auto exhaustive = _salg->getOptions().exhaustiveDemodulation();// && cl->length()==1 && (*cl)[0]->isEquality() && (*cl)[0]->isNegative();

  //Perhaps it might be a good idea to try to
  //replace subterms in some special order, like
  //the heaviest first...

  _attempted.reset();
  Term* lastDemodulated = nullptr;

  unsigned cLen=cl->length();
  for(unsigned li=0;li<cLen;li++) {
    Literal* lit=(*cl)[li];
    typename std::conditional<!combinatorySupSupport,
      NonVariableNonTypeIterator,
      FirstOrderSubtermIt>::type it(lit);
    while(it.hasNext()) {
      TypedTermList trm = it.next();
      if(!_attempted.insert(trm)) {
        //We have already tried to demodulate the term @b trm and did not
        //succeed (otherwise we would have returned from the function).
        //If we have tried the term @b trm, we must have tried to
        //demodulate also its subterms, so we can skip them too.
        it.right();
        continue;
      }
      Stack<pair<Clause*,Clause*>> resPremisePairs;
      perform(trm, lit, cl, resPremisePairs, exhaustive);
      if (resPremisePairs.isNonEmpty()) {
        timer.stop();
        for (const auto& kv : resPremisePairs) {
          auto res = kv.first;
          auto premise = kv.second;
          if (!res) {
            ASS(premise);
            ASS(!exhaustive);
            return pvi(getSingletonIterator(make_pair((Clause*)nullptr,pvi(getSingletonIterator(premise)))));
          }
          resIt = pvi(getConcatenatedIterator(resIt,pvi(getSingletonIterator(make_pair(res,pvi(getSingletonIterator(premise)))))));
        }

        if (!exhaustive) {
          return resIt;
        }
        lastDemodulated = trm.term();
        it.reset(trm.term());
      }
    }
  }

  if (lastDemodulated) {
    ASS(exhaustive);
    ASS_EQ(cLen,1);
    Literal* lit=(*cl)[0];
    typename std::conditional<!combinatorySupSupport,
      NonVariableNonTypeIterator,
      FirstOrderSubtermIt>::type it(lit);
    while(it.hasNext()) {
      TypedTermList trm = it.next();
      if(!_attempted.insert(trm) || !trm.containsSubterm(TermList(lastDemodulated))) {
        it.right();
        continue;
      }
      Stack<pair<Clause*,Clause*>> resPremisePairs;
      perform(trm, lit, cl, resPremisePairs, exhaustive);
      for (const auto& kv : resPremisePairs) {
        auto res = kv.first;
        auto premise = kv.second;
        ASS(res);
        resIt = pvi(getConcatenatedIterator(resIt,pvi(getSingletonIterator(make_pair(res,pvi(getSingletonIterator(premise)))))));
      }
    }
    handleSubtermsForBackwardDemodulation(cl, lastDemodulated, _bwIndex);
  }

  return resIt;
}

template <bool combinatorySupSupport>
void ForwardDemodulationImpl<combinatorySupSupport>::perform(TypedTermList trm, Literal* lit, Clause* cl,
  Stack<pair<Clause*,Clause*>>& resPremisePairs, bool exhaustive)
{
  const auto& ordering = _salg->getOrdering();
  unsigned cLen = cl->length();
  bool toplevelCheck = _redundancyCheck &&
    lit->isEquality() && (trm==*lit->nthArgument(0) || trm==*lit->nthArgument(1));

  // encompassing demodulation is always fine into negative literals or into non-units
  if (_encompassing) {
    toplevelCheck &= lit->isPositive() && (cLen == 1);
  }

  TermQueryResultIterator git=_index->getGeneralizations(trm, true);
  while(git.hasNext()) {
    TermQueryResult qr=git.next();
    ASS_EQ(qr.clause->length(),1);

    if(!ColorHelper::compatible(cl->color(), qr.clause->color())) {
      continue;
    }

    // to deal with polymorphic matching
    // Ideally, we would like to extend the substitution
    // returned by the index to carry out the sort match.
    // However, ForwardDemodulation uses a CodeTree as its
    // indexing mechanism, and it is not clear how to extend
    // the substitution returned by a code tree.
    static RobSubstitution subst;
    bool resultTermIsVar = qr.term.isVar();
    if(resultTermIsVar){
      TermList querySort = trm.sort();
      TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
      subst.reset();
      if(!subst.match(eqSort, 0, querySort, 1)){
        continue;
      }
    }

    TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
    TermList rhsS;
    if(!qr.substitution->isIdentityOnQueryWhenResultBound()) {
      //When we apply substitution to the rhs, we get a term, that is
      //a variant of the term we'd like to get, as new variables are
      //produced in the substitution application.
      TermList lhsSBadVars=qr.substitution->applyToResult(qr.term);
      TermList rhsSBadVars=qr.substitution->applyToResult(rhs);
      Renaming rNorm, qNorm, qDenorm;
      rNorm.normalizeVariables(lhsSBadVars);
      qNorm.normalizeVariables(trm);
      qDenorm.makeInverse(qNorm);
      ASS_EQ(trm,qDenorm.apply(rNorm.apply(lhsSBadVars)));
      rhsS=qDenorm.apply(rNorm.apply(rhsSBadVars));
    } else {
      rhsS=qr.substitution->applyToBoundResult(rhs);
    }
    if(resultTermIsVar){
      rhsS = subst.apply(rhsS, 0);
    }

    Ordering::Result argOrder = ordering.getEqualityArgumentOrder(qr.literal);
    bool preordered = argOrder==Ordering::LESS || argOrder==Ordering::GREATER;
#if VDEBUG
    if(preordered) {
      if(argOrder==Ordering::LESS) {
        ASS_EQ(rhs, *qr.literal->nthArgument(0));
      }
      else {
        ASS_EQ(rhs, *qr.literal->nthArgument(1));
      }
    }
#endif
    if(!preordered && (_preorderedOnly || ordering.compare(trm,rhsS)!=Ordering::GREATER) ) {
      continue;
    }

    // encompassing demodulation is fine when rewriting the smaller guy
    if (toplevelCheck && _encompassing) {
      // this will only run at most once;
      // could have been factored out of the getGeneralizations loop,
      // but then it would run exactly once there
      Ordering::Result litOrder = ordering.getEqualityArgumentOrder(lit);
      if ((trm==*lit->nthArgument(0) && litOrder == Ordering::LESS) ||
          (trm==*lit->nthArgument(1) && litOrder == Ordering::GREATER)) {
        toplevelCheck = false;
      }
    }

    if(toplevelCheck) {
      TermList other=EqHelper::getOtherEqualitySide(lit, trm);
      Ordering::Result tord=ordering.compare(rhsS, other);
      if(tord!=Ordering::LESS && tord!=Ordering::LESS_EQ) {
        if (_encompassing) {
          // last chance, if the matcher is not a renaming
          if (qr.substitution->isRenamingOn(qr.term,true /* we talk of result term */)) {
            continue; // under _encompassing, we know there are no other literals in cl
          }
        } else {
          Literal* eqLitS=qr.substitution->applyToBoundResult(qr.literal);
          bool isMax=true;
          Clause::Iterator cit(*cl);
          while(cit.hasNext()) {
            Literal* lit2=cit.next();
            if(lit==lit2) {
              continue;
            }
            if(ordering.compare(eqLitS, lit2)==Ordering::LESS) {
              isMax=false;
              break;
            }
          }
          if(isMax) {
            //RSTAT_CTR_INC("tlCheck prevented");
            //The demodulation is this case which doesn't preserve completeness:
            //s = t     s = t1 \/ C
            //---------------------
            //     t = t1 \/ C
            //where t > t1 and s = t > C
            continue;
          }
        }
      }
    }

    Literal* resLit = EqHelper::replace(lit,trm,rhsS);
    if(EqHelper::isEqTautology(resLit)) {
      ASS(!exhaustive);
      env.statistics->forwardDemodulationsToEqTaut++;
      resPremisePairs.push(make_pair(nullptr,qr.clause));
      return;
    }

    Clause* res = new(cLen) Clause(cLen,
      SimplifyingInference2(InferenceRule::FORWARD_DEMODULATION, cl, qr.clause));
    (*res)[0]=resLit;

    unsigned next=1;
    for(unsigned i=0;i<cLen;i++) {
      Literal* curr=(*cl)[i];
      if(curr!=lit) {
        (*res)[next++] = curr;
      }
    }
    ASS_EQ(next,cLen);

    env.statistics->forwardDemodulations++;
    resPremisePairs.push(make_pair(res,qr.clause));
    if (!exhaustive) {
      return;
    }
  }
}

// This is necessary for templates defined in cpp files.
// We are happy to do it for ForwardDemodulationImpl, since it (at the moment) has only two specializations:
template class ForwardDemodulationImpl<false>;
template class ForwardDemodulationImpl<true>;

}
