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

struct State {
  vvector<unsigned> litsSD;
  vvector<unsigned> litsSR;

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

struct BindingBO : public BacktrackObject
{
  BindingBO(Substitution& subst, unsigned var) : _subst(subst), _var(var) {}
  void backtrack() { _subst.unbind(_var); }

  CLASS_NAME(BindingBO);
  USE_ALLOCATOR(BindingBO);

  Substitution& _subst;
  unsigned _var;
};

struct SetBoolBO : public BacktrackObject
{
  SetBoolBO(vvector<bool>& v, unsigned i) : _v(v), _i(i) {}
  void backtrack() { _v[_i] = true; }

  CLASS_NAME(SetBoolBO);
  USE_ALLOCATOR(SetBoolBO);

  vvector<bool>& _v;
  unsigned _i;
};

struct ValueSetBO : public BacktrackObject
{
  ValueSetBO(unsigned& ref, unsigned v) : _ref(ref), _v(v) {}
  void backtrack() { _ref = _v; }

  CLASS_NAME(ValueSetBO);
  USE_ALLOCATOR(ValueSetBO);

  unsigned& _ref;
  unsigned _v;
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
      size_t lenSR = premise->length();
      const auto& premiseLo = premise->getLiteralOrder(ord);
      vmap<pair<unsigned,unsigned>,pair<bool,Substitution>> cache;

      // cout << *qr.literal << " matched " << *((*cl)[li]) << endl;
      // State s;


      // the state:
      // current indices of matcher and matched literals
      unsigned iSR = 0;
      unsigned iSD = 0;
      auto currSR = premise->getLiteralPosition(qr.literal);
      unsigned currSD = li;
      if (lenSR == 1) {
        // unit subsumption
        return true;
      }

      // remaining lits of subsumer, initially all true except currently matched
      vvector<bool> litsSR(lenSR, true);
      litsSR[currSR] = false;

      // remaining lits of subsumed, initially set below
      vvector<bool> litsSD(clen, false);
      for (unsigned j = 0; j < clen; j++) {
        if (currSD != j && GorGEorIC(clLo,currSD,j)) {
          litsSD[j] = true;
        }
      }
      // current partial order within lits of subsumer
      TriangularArray<Ordering::Result> litOrderSR(lenSR); // TODO copy from premiseLo

      // current matching substitution
      Substitution subst;
      VariableIterator it(qr.literal);
      ASS(qr.substitution->isIdentityOnQueryWhenResultBound());
      while(it.hasNext()) {
        TermList v = it.next();
        ASS(v.isVar());
        subst.rebind(v.var(), qr.substitution->applyToBoundResult(v));
      }
      Stack<BacktrackData> bds;

      // cout << "match " << *premise << endl
      //      << "   to " << *cl << endl << endl;
      Substitution newSubst;
      Binder binder(newSubst);
      while (true) {
        // choose next possible match
        bool found = false;
        for (unsigned i = iSR; i < lenSR; i++) {
          if (!litsSR[i]) {
            continue;
          }
          for (unsigned j = (i==iSR) ? iSD : 0; j < clen; j++) {
            if (!litsSD[j]) {
              continue;
            }
            // cout << "trying to match " << i << " with " << j << endl;
            if (!MatchingUtils::match((*premise)[i], (*cl)[j], false, binder)) {
              continue;
            }
            BacktrackData localBD;
            auto it = newSubst.iterator();
            while (it.hasNext()) {
              unsigned v;
              TermList t;
              it.next(v,t);
              TermList temp;
              if (subst.findBinding(v,temp)) {
                if (temp!=t) {
                  // cout << "nomatch1" << endl;
                  goto nomatch;
                }
              } else {
                subst.bind(v,t);
                localBD.addBacktrackObject(new BindingBO(subst, v));
              }
            }
            // check arrays
            {
              bool anyLeft = false;
              for (unsigned k = 0; k < lenSR; k++) {
                if (i == k || !litsSR[k]) {
                  continue;
                }
                anyLeft = true;
                if (!GorGEorIC(premiseLo,i,k)) {
                  // cout << "nomatch2" << endl;
                  goto nomatch;
                }
              }
              if (!anyLeft) {
                // subsumption
                // if (lenSR == 1) {
                //   cout << "unit subsumption" << endl;
                // }
                env.statistics->newForwardSubsumed++;
                if (!checkSubsumption(cl, premise)) {
                  cout << "wrong subsumption " << *cl << endl 
                       << "by                " << *premise << endl;
                }
                return true;
              }
              // cout << "setting false litsSR " << i << endl;
              litsSR[i] = false;
              localBD.addBacktrackObject(new SetBoolBO(litsSR,i));

              anyLeft = false;
              for (unsigned k = 0; k < clen; k++) {
                if (j == k || !GorGEorIC(clLo,j,k)) {
                  // cout << "setting false litsSD " << k << endl;
                  litsSD[k] = false;
                  localBD.addBacktrackObject(new SetBoolBO(litsSD,k));
                } else {
                  anyLeft = true;
                }
              }
              if (!anyLeft) {
                  // cout << "nomatch3" << endl;
                goto nomatch;
              }
            }
            found = true;
            localBD.addBacktrackObject(new ValueSetBO(iSR,i));
            localBD.addBacktrackObject(new ValueSetBO(iSD,j+1));
            iSR = 0;
            iSD = 0;
            bds.push(localBD);
            goto fin;

            nomatch:
              localBD.backtrack();            
          }
        }
      fin:
        // if no new match found we have nothing in bd
        if (!found) {
          if (bds.isEmpty()) {
            // fail
            // cout << "fail" << endl;
            goto fail;
          }
          // otherwise backtrack
          // cout << "backtrack" << endl;
          auto bd = bds.pop();
          bd.backtrack();
          continue;
        }
      }

      fail: continue;

      // {
      //   TIME_TRACE("init");
      //   // get substitution
      //   VariableIterator it(qr.literal);
      //   ASS(qr.substitution->isIdentityOnQueryWhenResultBound());
      //   while(it.hasNext()) {
      //     TermList v = it.next();
      //     ASS(v.isVar());
      //     s.subst.rebind(v.var(), qr.substitution->applyToBoundResult(v));
      //     subst.rebind(v.var(), qr.substitution->applyToBoundResult(v));
      //   }
      //   // get available literals from both clauses
      //   auto currSR = premise->getLiteralPosition(qr.literal);
      //   for (unsigned j = 0; j < premise->length(); j++) {
      //     if (j != currSR) {
      //       // cout << "insertSR " << j << endl;
      //       s.litsSR.push_back(j);
      //     }
      //   }
      //   for (unsigned j = 0; j < clen; j++) {
      //     if (li != j && GorGEorIC(clLo,li,j)) {
      //       // cout << "insertSD " << j << endl;
      //       s.litsSD.push_back(j);
      //     }
      //   }
      // }

      // Stack<BacktrackData> bds;
      // Stack<State> todo;
      // todo.push(s);

      // // cout << "cl " << *cl << endl << "premise " << *premise << endl;
      // // cout << s.litsSR.size() << " " << s.litsSD.size() << endl << endl;

      // while (todo.isNonEmpty()) {
      //   auto s = todo.pop();
      //   if (s.litsSR.empty()) {
      //     TIME_TRACE("subsumption aftercheck");
      //     if (!checkSubsumption(cl, premise)) {
      //       cout << "wrong subsumption " << *cl << endl 
      //            << "by                " << *premise << endl;
      //     }
      //     env.statistics->newForwardSubsumed++;
      //     return true;
      //   }
      //   if (s.litsSD.empty()) {
      //     continue;
      //   }

      //   // cout << s.litsSD.size()*s.litsSR.size() << endl;
      //   for (const auto& lSD : s.litsSD) {
      //     for (const auto& lSR : s.litsSR) {
      //       TIME_TRACE("match try");
      //       auto p = make_pair(lSR,lSD);
      //       if (cache.count(p) == 0) {
      //         cache.insert(make_pair(p,make_pair(false,Substitution())));
      //         auto& ref = cache.at(p);
      //         Binder binder(ref.second);
      //         // cout << "try " << *(*premise)[lSR] << " with " << *(*cl)[lSD] << endl;
      //         if (!MatchingUtils::match((*premise)[lSR], (*cl)[lSD], false, binder)) {
      //           // binder.reset();
      //           continue;
      //         }
      //         ref.first = true;
      //       }

      //       auto& ref = cache.at(p);
      //       if (!ref.first) {
      //         continue;
      //       }
      //       TIME_TRACE("add next");
      //       State next;
      //       auto it = ref.second.iterator();
      //       while (it.hasNext()) {
      //         unsigned v;
      //         TermList t;
      //         it.next(v,t);
      //         next.subst.bind(v,t);
      //       }
      //       it = s.subst.iterator();
      //       bool match = true;
      //       while (it.hasNext()) {
      //         unsigned v;
      //         TermList t;
      //         it.next(v,t);
      //         TermList temp;
      //         if (next.subst.findBinding(v,temp)) {
      //           if (temp!=t) {
      //             match = false;
      //             break;
      //           }
      //         } else {
      //           next.subst.bind(v,t);
      //         }
      //       }
      //       if (!match) {
      //         // cout << "fail" << endl;
      //         continue;
      //       }
      //       for (const auto& liSR : s.litsSR) {
      //         if (liSR != lSR && GorGEorIC(premiseLo,lSR,liSR)) {
      //           // cout << "insertSR " << liSR << endl;
      //           next.litsSR.push_back(liSR);
      //         }
      //       }
      //       // we lost some literals on the way, fail
      //       if (next.litsSR.size() != s.litsSR.size()-1) {
      //         // cout << "fail" << endl;
      //         continue;
      //       }
      //       for (const auto& liSD : s.litsSD) {
      //         if (liSD != lSD && GorGEorIC(clLo,lSD,liSD)) {
      //           // cout << "insertSD " << liSD << endl;
      //           next.litsSD.push_back(liSD);
      //         }
      //       }
      //       todo.push(next);
      //     }
      //   }
      // }
    }
  }
  return false;
}

} // namespace Inferences
