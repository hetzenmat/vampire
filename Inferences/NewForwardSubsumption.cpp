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
#include "Kernel/MLMatcher.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
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

struct ClauseMatches {
  CLASS_NAME(ForwardSubsumptionAndResolution::ClauseMatches);
  USE_ALLOCATOR(ClauseMatches);

private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
  ClauseMatches(const ClauseMatches &);
  ClauseMatches &operator=(const ClauseMatches &);

public:
  ClauseMatches(Clause *cl) : _cl(cl), _zeroCnt(cl->length())
  {
    unsigned clen = _cl->length();
    _matches = static_cast<LiteralList **>(ALLOC_KNOWN(clen * sizeof(void *), "Inferences::ClauseMatches"));
    for (unsigned i = 0; i < clen; i++) {
      _matches[i] = 0;
    }
  }
  ~ClauseMatches()
  {
    unsigned clen = _cl->length();
    for (unsigned i = 0; i < clen; i++) {
      LiteralList::destroy(_matches[i]);
    }
    DEALLOC_KNOWN(_matches, clen * sizeof(void *), "Inferences::ClauseMatches");
  }

  void addMatch(Literal *baseLit, Literal *instLit)
  {
    addMatch(_cl->getLiteralPosition(baseLit), instLit);
  }
  void addMatch(unsigned bpos, Literal *instLit)
  {
    if (!_matches[bpos]) {
      _zeroCnt--;
    }
    LiteralList::push(instLit, _matches[bpos]);
  }
  void fillInMatches(LiteralMiniIndex *miniIndex)
  {
    unsigned blen = _cl->length();

    for (unsigned bi = 0; bi < blen; bi++) {
      LiteralMiniIndex::InstanceIterator instIt(*miniIndex, (*_cl)[bi], false);
      while (instIt.hasNext()) {
        Literal *matched = instIt.next();
        addMatch(bi, matched);
      }
    }
  }
  bool anyNonMatched() { return _zeroCnt; }

  Clause *_cl;
  unsigned _zeroCnt;
  LiteralList **_matches;

  class ZeroMatchLiteralIterator {
  public:
    ZeroMatchLiteralIterator(ClauseMatches *cm)
        : _lits(cm->_cl->literals()), _mlists(cm->_matches), _remaining(cm->_cl->length())
    {
      if (!cm->_zeroCnt) {
        _remaining = 0;
      }
    }
    bool hasNext()
    {
      while (_remaining > 0 && *_mlists) {
        _lits++;
        _mlists++;
        _remaining--;
      }
      return _remaining;
    }
    Literal *next()
    {
      _remaining--;
      _mlists++;
      return *(_lits++);
    }

  private:
    Literal **_lits;
    LiteralList **_mlists;
    unsigned _remaining;
  };
};

bool checkSubsumption(Clause* cl, Clause* premise)
{
  LiteralMiniIndex miniIndex(cl);

  ClauseMatches *cms = new ClauseMatches(premise);
  cms->fillInMatches(&miniIndex);

  if (cms->anyNonMatched()) {
    return false;
  }

  return MLMatcher::canBeMatched(premise, cl, cms->_matches, 0);
}

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
      vmap<pair<unsigned,unsigned>,pair<bool,Substitution>> cache;

      // cout << *qr.literal << " matched " << *((*cl)[li]) << endl;
      State s;
      {
        TIME_TRACE("init");
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
            // cout << "insertSR " << j << endl;
            s.litsSR.insert(j);
          }
        }
        for (unsigned j = 0; j < clen; j++) {
          if (li != j && GorGEorIC(clLo,li,j)) {
            // cout << "insertSD " << j << endl;
            s.litsSD.insert(j);
          }
        }
      }

      Stack<State> todo;
      todo.push(s);

      // cout << "cl " << *cl << endl << "premise " << *premise << endl;
      // cout << s.litsSR.size() << " " << s.litsSD.size() << endl << endl;

      while (todo.isNonEmpty()) {
        auto s = todo.pop();
        if (s.litsSR.empty()) {
          TIME_TRACE("unit subsumption?");
          if (premise->length() > 1) {
            TIME_TRACE("non-unit subsumption");
          }
          if (!checkSubsumption(cl, premise)) {
            cout << "wrong subsumption " << *cl << endl 
                 << "by                " << *premise << endl;
          }
          return true;
        }
        if (s.litsSD.empty()) {
          continue;
        }

        for (const auto& lSD : s.litsSD) {
          for (const auto& lSR : s.litsSR) {
            // TIME_TRACE("match try");
            auto p = make_pair(lSR,lSD);
            if (cache.count(p) == 0) {
              cache.insert(make_pair(p,make_pair(false,Substitution())));
              auto& ref = cache.at(p);
              Binder binder(ref.second);
              // cout << "try " << *(*premise)[lSR] << " with " << *(*cl)[lSD] << endl;
              if (!MatchingUtils::match((*premise)[lSR], (*cl)[lSD], false, binder)) {
                // binder.reset();
                continue;
              }
              ref.first = true;
            }

            auto& ref = cache.at(p);
            if (!ref.first) {
              continue;
            }
            State next;
            auto it = ref.second.iterator();
            while (it.hasNext()) {
              unsigned v;
              TermList t;
              it.next(v,t);
              next.subst.bind(v,t);
            }
            it = s.subst.iterator();
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
              // cout << "fail" << endl;
              continue;
            }
            for (const auto& liSR : s.litsSR) {
              if (liSR != lSR && GorGEorIC(premiseLo,lSR,liSR)) {
                // cout << "insertSR " << liSR << endl;
                next.litsSR.insert(liSR);
              }
            }
            // we lost some literals on the way, fail
            if (next.litsSR.size() != s.litsSR.size()-1) {
              // cout << "fail" << endl;
              continue;
            }
            for (const auto& liSD : s.litsSD) {
              if (liSD != lSD && GorGEorIC(clLo,lSD,liSD)) {
                // cout << "insertSD " << liSD << endl;
                next.litsSD.insert(liSD);
              }
            }
            todo.push(next);
          }
        }
      }
    }
  }
  return false;
}

} // namespace Inferences
