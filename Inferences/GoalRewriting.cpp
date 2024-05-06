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
 * @file GoalRewriting.cpp
 * Implements class GoalRewriting.
 */

#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/TermIndex.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "GoalRewriting.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace std;

void GoalRewriting::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex=static_cast<TermIndex<TermLiteralClause>*>(
	  _salg->getIndexManager()->request(GOAL_REWRITING_LHS_INDEX) );
  _subtermIndex=static_cast<TermIndex<TermLiteralClause>*>(
	  _salg->getIndexManager()->request(GOAL_REWRITING_SUBTERM_INDEX) );
}

void GoalRewriting::detach()
{
  _lhsIndex = 0;
  _subtermIndex=0;
  _salg->getIndexManager()->release(GOAL_REWRITING_LHS_INDEX);
  _salg->getIndexManager()->release(GOAL_REWRITING_SUBTERM_INDEX);
  GeneratingInferenceEngine::detach();
}

TermList replaceOccurrence(Term* t, const Term* orig, TermList repl, const Position& pos)
{
  Stack<pair<Term*,unsigned>> todo;
  Term* curr = t;
  for (unsigned i = 0; i < pos.size(); i++) {
    auto p = pos[i];
    ASS_L(p,curr->arity());
    todo.push(make_pair(curr,p));

    auto next = curr->nthArgument(p);
    ASS(next->isTerm());
    curr = next->term();
  }
  ASS_EQ(orig,curr);
  TermList res = repl;

  while(todo.isNonEmpty()) {
    auto kv = todo.pop();
    TermStack args; 
    for (unsigned i = 0; i < kv.first->arity(); i++) {
      if (i == kv.second) {
        args.push(TermList(res));
      } else {
        args.push(*kv.first->nthArgument(i));
      }
    }
    res = TermList(Term::create(kv.first,args.begin()));
  }
  return res;
}

pair<Term*,Stack<unsigned>> PositionalNonVariableNonTypeIterator::next()
{
  auto kv = _stack.pop();
  TermList* ts;
  auto t = kv.first;

  for(unsigned i = t->numTypeArguments(); i < t->arity(); i++){
    ts = t->nthArgument(i);
    if (ts->isTerm()) {
      auto newPos = kv.second;
      newPos.push(i);
      _stack.push(make_pair(const_cast<Term*>(ts->term()),std::move(newPos)));
    }
  }
  return kv;
}

VirtualIterator<pair<Term*,Position>> getPositions(TermList t, const Term* st)
{
  if (t.isVar()) {
    return VirtualIterator<pair<Term*,Position>>::getEmpty();
  }
  return pvi(iterTraits(vi(new PositionalNonVariableNonTypeIterator(t.term())))
    .filter([st](pair<Term*,Position> arg) {
      return arg.first == st;
    }));
}

VirtualIterator<TypedTermList> sideIterator(Literal* lit)
{
  auto res = VirtualIterator<TypedTermList>::getEmpty();
  for (unsigned i = 0; i <= 1; i++) {
    auto lhs = lit->termArg(i);
    auto rhs = lit->termArg(1-i);
    if (lhs.containsAllVariablesOf(rhs)) {
      res = pvi(concatIters(res, pvi(getSingletonIterator(TypedTermList(lhs,SortHelper::getEqualityArgumentSort(lit))))));
    }
  }
  return res;
}

ClauseIterator GoalRewriting::generateClauses(Clause* premise)
{
  auto res = ClauseIterator::getEmpty();

  if (premise->length()!=1 || premise->goalRewritingDepth()>=_salg->getOptions().maxGoalRewritingDepth()) {
    return res;
  }

  auto lit = (*premise)[0];
  if (!lit->isEquality()) {
    return res;
  }

  const auto& opt = _salg->getOptions();

  // forward
  if (lit->isNegative() && lit->ground()) {
    res = pvi(iterTraits(getUniquePersistentIterator(vi(new NonVariableNonTypeIterator(lit))))
      .unique()
      .flatMap([this](Term* t) {
        return pvi(pushPairIntoRightIterator(t,_lhsIndex->getGeneralizations(t, true)));
      })
      .filter([premise,&opt](pair<Term*,QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg) {
        auto qr = arg.second;
        if (premise->goalRewritingDepth()+qr.data->clause->goalRewritingDepth()>=opt.maxGoalRewritingDepth()) {
          return false;
        }
        return SortHelper::getResultSort(arg.first) == SortHelper::getEqualityArgumentSort(qr.data->literal);
      })
      .flatMap([lit](pair<Term*,QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg) {
        auto t0 = lit->termArg(0);
        auto t1 = lit->termArg(1);
        return pushPairIntoRightIterator(arg.second,
          pvi(concatIters(
            pvi(pushPairIntoRightIterator(t0.term(),getPositions(t0,arg.first))),
            pvi(pushPairIntoRightIterator(t1.term(),getPositions(t1,arg.first)))
          )));
      })
      .map([lit,premise,this](pair<QueryRes<ResultSubstitutionSP, TermLiteralClause>,pair<Term*,pair<Term*,Position>>> arg) -> Clause* {
        auto side = arg.second.first;
        auto lhsS = arg.second.second.first;
        auto pos = arg.second.second.second;
        auto qr = arg.first;
        return perform(premise,lit,side,lhsS,std::move(pos),qr.data->clause,qr.data->literal,qr.data->term,qr.unifier.ptr(),true);
      })
      .filter(NonzeroFn()));
  }

  // backward
  if (lit->isPositive()) {
    res = pvi(concatIters(res,pvi(iterTraits(sideIterator(lit))
      .flatMap([this](TypedTermList lhs) {
        return pvi(pushPairIntoRightIterator(lhs,_subtermIndex->getInstances(lhs,true)));
      })
      .filter([premise,lit,&opt](pair<TypedTermList,QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg) {
        auto qr = arg.second;
        if (premise->goalRewritingDepth()+qr.data->clause->goalRewritingDepth()>=opt.maxGoalRewritingDepth()) {
          return false;
        }
        return SortHelper::getResultSort(qr.data->term.term()) == SortHelper::getEqualityArgumentSort(lit);
      })
      .flatMap([](pair<TypedTermList,QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg) {
        auto t = arg.second.data->term.term();
        auto t0 = arg.second.data->literal->termArg(0);
        auto t1 = arg.second.data->literal->termArg(1);
        return pushPairIntoRightIterator(arg,
          pvi(concatIters(
            pvi(pushPairIntoRightIterator(t0.term(),getPositions(t0,t))),
            pvi(pushPairIntoRightIterator(t1.term(),getPositions(t1,t)))
          )));
      })
      .map([lit,premise,this](pair<pair<TypedTermList,QueryRes<ResultSubstitutionSP, TermLiteralClause>>,pair<Term*,pair<Term*,Position>>> arg) -> Clause* {
        auto side = arg.second.first;
        auto pos = arg.second.second.second;
        auto qr = arg.first.second;
        auto eqLhs = arg.first.first;
        return perform(qr.data->clause, qr.data->literal, side, qr.data->term.term(), std::move(pos), premise, lit, eqLhs, qr.unifier.ptr(), false);
      })
      .filter(NonzeroFn()))));
  }
  auto resTT = TIME_TRACE_ITER("goal rewriting", res);
  return pvi(resTT);
}

Clause* GoalRewriting::perform(Clause* rwClause, Literal* rwLit, Term* rwSide, const Term* rwTerm, Position&& pos,
  Clause* eqClause, Literal* eqLit, TermList eqLhs, ResultSubstitution* subst, bool eqIsResult)
{
  auto rhs = EqHelper::getOtherEqualitySide(eqLit,TermList(eqLhs));
  auto rhsS = eqIsResult ? subst->applyToBoundResult(rhs) : subst->applyToBoundQuery(rhs);

  auto tgtSide = replaceOccurrence(rwSide, rwTerm, rhsS, pos).term();
  auto other = EqHelper::getOtherEqualitySide(rwLit, TermList(rwSide));
  ASS_NEQ(tgtSide,other.term());
  auto resLit = Literal::createEquality(false, TermList(tgtSide), other, SortHelper::getEqualityArgumentSort(rwLit));

  Clause* res = new(1) Clause(1,
    GeneratingInference2(InferenceRule::GOAL_REWRITING, rwClause, eqClause));
  (*res)[0]=resLit;
  res->setGoalRewritingDepth(rwClause->goalRewritingDepth()+eqClause->goalRewritingDepth()+1);

  env.statistics->goalRewritings++;
  return res;
}

}