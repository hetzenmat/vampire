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
 * @file UnitEqualityCC.cpp
 * Implements class UnitEqualityCC.
 */

#include "UnitEqualityCC.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

void UnitEqualityCC::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex = static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
}

void UnitEqualityCC::detach()
{
  _lhsIndex = nullptr;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  GeneratingInferenceEngine::detach();
}

ClauseIterator UnitEqualityCC::generateClauses(Clause* premise)
{
  TIME_TRACE("unit equality cc");

  Stack<Term*> unprocessed;
  swap(_unprocessedGroundTerms, unprocessed);

  {TIME_TRACE("unprocessed");
  while (unprocessed.isNonEmpty()) {
    auto t = unprocessed.pop();
    handleGroundTerm(t);
  }}

  if (premise->length()>1) {
    return ClauseIterator::getEmpty();
  }

  auto lit = (*premise)[0];
  if (!lit->isEquality()) {
    return ClauseIterator::getEmpty();
  }

  if (lit->isNegative()) {
    ASS(lit->ground());
    if (_groundLitToClauseMap.insert(lit,premise)) {
      _cc.addLiteral(lit);
      NonVariableNonTypeIterator nvi(lit);
      while (nvi.hasNext()) {
        auto st = nvi.next();
        handleGroundTerm(st);
      }
    }
  } else {
    const auto& ord = _salg->getOrdering();
    for (unsigned i = 0; i <= 1; i++) {
      auto lhs = lit->termArg(i);
      auto rhs = lit->termArg(1-i);
      if (lhs.isVar() || !lhs.containsAllVariablesOf(rhs)) {
        continue;
      }
      auto it = _tis.getInstances(lhs.term(), true);
      while (it.hasNext()) {
        auto qr = it.next();
        auto lhsS = qr.term;
        auto litS = qr.substitution->applyToBoundQuery(lit);
        auto rhsS = EqHelper::getOtherEqualitySide(litS,lhsS);
        if (ord.compare(lhsS,rhsS)==Ordering::Result::GREATER) {
          handleEquality(litS, premise);
        }
      }
    }
  }

  switch (_cc.getStatus(false))
  {
  case DecisionProcedure::Status::UNKNOWN: {
    cout << "unknown" << endl;
    break;
  }
  case DecisionProcedure::Status::SATISFIABLE: {
    // cout << "sat" << endl;
    break;
  }
  case DecisionProcedure::Status::UNSATISFIABLE: {
    LiteralStack lits;
    _cc.getUnsatCore(lits,0);
    auto premises = UnitList::empty();
    for (const auto& lit : lits) {
      auto ptr = _groundLitToClauseMap.findPtr(lit);
      ASS(ptr);
      UnitList::push(*ptr,premises);
    }
    Clause* res = new(0) Clause(0,
      SimplifyingInferenceMany(InferenceRule::FORWARD_DEMODULATION, premises));
    return pvi(getSingletonIterator(res));
  }
  }

  return ClauseIterator::getEmpty();
}

void UnitEqualityCC::handleEquality(Literal* lit, Clause* cl)
{
  ASS(lit->ground() && lit->isEquality() && lit->isPositive());

  if (!_groundLitToClauseMap.insert(lit,cl)) {
    return;
  }

  _cc.addLiteral(lit);
  NonVariableNonTypeIterator nvi(lit);
  while (nvi.hasNext()) {
    auto st = nvi.next();
    if (_groundTerms.find(st)) {
      nvi.right();
      continue;
    }
    _unprocessedGroundTerms.push(st);
  }
}

void UnitEqualityCC::handleGroundTerm(Term* t)
{
  ASS(t->ground());

  if (!_groundTerms.insert(t)) {
    return;
  }
  if (_groundTerms.size() % 100 == 0) {
    cout << _groundTerms.size() << endl;
  }
  _tis.insert(t, nullptr, nullptr);

  auto it = _lhsIndex->getGeneralizations(t, true);
  while (it.hasNext()) {
    auto qr = it.next();
    auto litS = qr.substitution->applyToBoundResult(qr.literal);
    ASS(litS->ground());
    handleEquality(litS, qr.clause);
  }
}

}
