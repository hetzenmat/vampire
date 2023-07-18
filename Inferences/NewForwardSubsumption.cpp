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
 * @file NewForwardSubsumption.cpp
 * Implements class NewForwardSubsumption.
 */

#include "Kernel/Matcher.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "NewForwardSubsumption.hpp"

namespace Inferences {
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void NewForwardSubsumption::attach(SaturationAlgorithm *salg)
{
  CALL("NewForwardSubsumption::attach");
  ForwardSimplificationEngine::attach(salg);
  _index = static_cast<MaximalLiteralForwardSubsumptionIndex*>(
      _salg->getIndexManager()->request(MAXIMAL_FW_SUBSUMPTION_SUBST_TREE));
}

void NewForwardSubsumption::detach()
{
  CALL("NewForwardSubsumption::detach");
  _index = nullptr;
  _salg->getIndexManager()->release(MAXIMAL_FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}

inline bool GorGEorIC(const TriangularArray<Ordering::Result>& array, unsigned i, unsigned j) {
  Ordering::Result comp = i > j ? array.get(i,j) : array.get(j,i);
  if (i > j) {
    return comp == Ordering::Result::LESS || comp == Ordering::Result::LESS_EQ || comp == Ordering::Result::INCOMPARABLE;
  } else {
    return comp == Ordering::Result::GREATER || comp == Ordering::Result::GREATER_EQ || comp == Ordering::Result::INCOMPARABLE;
  }
}

struct State {
  vset<unsigned> litsSD;
  vset<unsigned> litsSR;

  Substitution subst;
};

struct Binder {
  Binder(Substitution& subst) : subst(subst) {}

  bool bind(unsigned var, TermList term)
  {
    TermList t;
    if (subst.findBinding(var, t)) {
      return false;
    }
    subst.bind(var,term);
    return true;
  }

  void reset() { subst.reset(); }
  void specVar(unsigned var, TermList term) { ASSERTION_VIOLATION; }

  Substitution& subst; 
};

bool NewForwardSubsumption::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  CALL("NewForwardSubsumption::perform");

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  TIME_TRACE("new forward subsumption");

  auto& ord = _salg->getOrdering();
  const auto& clLo = cl->getLiteralOrder(ord);

  for (unsigned li = 0; li < clen; li++) {
    SLQueryResultIterator rit = _index->getGeneralizations((*cl)[li], false, true);
    while (rit.hasNext()) {
      auto qr = rit.next();
      Clause *premise = qr.clause;
      const auto& premiseLo = premise->getLiteralOrder(ord);

      TIME_TRACE("init");
      // cout << *qr.literal << " matched " << *((*cl)[li]) << endl;
      State s;
      {
        // get substitution
        VariableIterator it(qr.literal);
        ASS(qr.substitution->isIdentityOnQueryWhenResultBound());
        while(it.hasNext()) {
          TermList v = it.next();
          ASS(v.isVar());
          s.subst.rebind(v.var(), qr.substitution->applyToBoundResult(v));
        }
        // get available literals from both clauses
        auto currSR = premise->getLiteralPosition(qr.literal);
        for (unsigned j = 0; j < premise->length(); j++) {
          if (j != currSR) {
            s.litsSR.insert(j);
          }
        }
        for (unsigned j = 0; j < clen; j++) {
          if (li != j && GorGEorIC(clLo,li,j)) {
            // cout << "insert " << j << endl;
            s.litsSD.insert(j);
          }
        }
      }

      Stack<State> todo;
      todo.push(s);

      // cout << "cl " << *cl << endl << "premise " << *premise << endl;
      // cout << s.litsSD.size() << endl << endl;

      while (todo.isNonEmpty()) {
        auto s = todo.pop();
        if (s.litsSR.empty()) {
          TIME_TRACE("unit subsumption?");
          if (premise->length() > 1) {
            TIME_TRACE("non-unit subsumption");
          }
          return true;
        }
        if (s.litsSD.empty()) {
          continue;
        }

        for (const auto& lSD : s.litsSD) {
          for (const auto& lSR : s.litsSR) {
            State next;
            Binder binder(next.subst);
            TIME_TRACE("match try");
            // cout << "try " << *(*premise)[lSR] << " with " << *(*cl)[lSD] << endl;
            if (MatchingUtils::match((*premise)[lSR], (*cl)[lSD], false, binder)) {
              // cout << "success" << endl;
              auto it = s.subst.iterator();
              bool match = true;
              while (it.hasNext()) {
                unsigned v;
                TermList t;
                it.next(v,t);
                TermList temp;
                if (next.subst.findBinding(v,temp)) {
                  if (temp!=t) {
                    match = false;
                    break;
                  }
                } else {
                  next.subst.bind(v,t);
                }
              }
              if (!match) {
                continue;
              }
              for (const auto& liSD : s.litsSD) {
                if (liSD != lSD && GorGEorIC(clLo,lSD,liSD)) {
                  next.litsSD.insert(liSD);
                }
              }
              for (const auto& liSR : s.litsSR) {
                if (liSR != lSR && GorGEorIC(premiseLo,lSR,liSR)) {
                  next.litsSR.insert(liSR);
                }
              }
              todo.push(next);
            } else {
              // cout << "fail" << endl;
              TIME_TRACE("match mismatch");
            }
          }
        }
      }
    }
  }
  return false;
}

} // namespace Inferences
