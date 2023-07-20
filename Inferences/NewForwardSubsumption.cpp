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
  _ctIndex = static_cast<CodeTreeSubsumptionIndex*>(
      _salg->getIndexManager()->request(FW_SUBSUMPTION_CODE_TREE));
}

void NewForwardSubsumption::detach()
{
  CALL("NewForwardSubsumption::detach");
  _ctIndex = nullptr;
  _index = nullptr;
  _salg->getIndexManager()->release(FW_SUBSUMPTION_CODE_TREE);
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
  TIME_TRACE("subsumption check");
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
      return t == term;
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
  void backtrack() { ASS(!_v[_i]); _v[_i] = true; }

  CLASS_NAME(SetBoolBO);
  USE_ALLOCATOR(SetBoolBO);

  vvector<bool>& _v;
  unsigned _i;
};

template<class T>
struct ValueSetBO : public BacktrackObject
{
  ValueSetBO(T& ref, T v) : _ref(ref), _v(v) {}
  void backtrack() { _ref = _v; }

  CLASS_NAME(ValueSetBO);
  USE_ALLOCATOR(ValueSetBO);

  T& _ref;
  T _v;
};

inline void unsetBoolBacktrack(BacktrackData& bd, vvector<bool>& ref, size_t i)
{
  ASS(ref[i]);
  ref[i] = false;
  bd.addBacktrackObject(new SetBoolBO(ref,i));
}

bool NewForwardSubsumption::perform(Clause *cl, Clause *&replacement, ClauseIterator &premises)
{
  CALL("NewForwardSubsumption::perform");

  unsigned clen = cl->length();
  if (clen == 0) {
    return false;
  }

  TIME_TRACE("new forward subsumption");

  auto it = _ctIndex->getSubsumingOrSResolvingClauses(cl, false);
  while (it.hasNext()) {
    auto qr = it.next();
    if (!checkSubsumption(cl, qr.clause)) {
      cout << "wrong subsumption " << *cl << endl 
           << "by                " << *qr.clause << endl;
    }
    env.statistics->newForwardSubsumed++;
    return true;
  }
  return false;

  auto& ord = _salg->getOrdering();
  const auto& clLo = cl->getLiteralOrder(ord);

  LiteralMiniIndex miniIndex(cl);
  static vset<pair<unsigned,unsigned>> _clPairs;

  for (unsigned li = 0; li < clen; li++) {
    SLQueryResultIterator rit = _index->getGeneralizations((*cl)[li], false, false);
    while (rit.hasNext()) {
      auto qr = rit.next();
      static unsigned cnt = 0;
      vstringstream debug;
      Clause *premise = qr.clause;
      if (!_clPairs.insert(make_pair(cl->number(),qr.clause->number())).second) {
        continue;
      }
      size_t lenSR = premise->length();
      const auto& premiseLo = premise->getLiteralOrder(ord);
      if (clen < premise->matchingMinimumLiteralCount(ord)) {
        TIME_TRACE("skipped by minimum matching literal count");
        continue;
      }

      // debug << *cl << " " << *premise << endl;
      // debug << "lits " << *(*cl)[li] << " " << *qr.literal << endl;

      // auto rowNonZero = [](const vvector<bool>& v) {
      //   unsigned cnt = 0;
      //   for (unsigned i = 0; i < v.size(); i++) {
      //     cnt += v[i];
      //   }
      //   return cnt;
      // };

      // auto outputMatches = [](const vvector<vvector<bool>>& v, ostream& out) {
      //   for (unsigned i = 0; i < v.size(); i++) {
      //     out << i << ": "; 
      //     for (unsigned j = 0; j < v[i].size(); j++) {
      //       out << v[i][j] << " ";
      //     }
      //     out << endl;
      //   }
      //   out << endl;
      // };

      vvector<vvector<bool>> matches(lenSR, vvector<bool>(clen, false));
      vvector<unsigned> matchesSetBits(lenSR, 0);
      bool anyNonMatched = false;
      for (unsigned i = 0; i < lenSR; i++) {
        LiteralMiniIndex::InstanceIterator instIt(miniIndex, (*premise)[i], false);
        while (instIt.hasNext()) {
          auto j = cl->getLiteralPosition(instIt.next());
          ASS(!matches[i][j]);
          matchesSetBits[i]++;
          matches[i][j] = true;
        }
        if (!matchesSetBits[i]) {
          anyNonMatched = true;
          break;
        }
      }
      if (anyNonMatched) {
        TIME_TRACE("nonmatched filter");
        continue;
      }

      if (lenSR == 1) {
        // unit subsumption
        env.statistics->newForwardSubsumed++;
        return true;
      }

      // the state:
      // current indices of matcher and matched literals
      unsigned iSR = 0;
      unsigned iSD = 0;

      // remaining lits of subsumer, initially all true
      vvector<bool> litsSR(lenSR, true);

      // remaining lits of subsumed, initially set true
      vvector<bool> litsSD(clen, true);

      // current matching substitution
      Substitution subst;
      Stack<BacktrackData> bds;

      Substitution newSubst;
      Binder binder(newSubst);
      while (true) {
        // choose next possible match
        bool found = false;
        for (unsigned i = iSR; i < lenSR; i++) {
          // cout << "i: " << i << endl;
          if (!litsSR[i]) {
            continue;
          }
          for (unsigned j = (i==iSR) ? iSD : 0; j < clen; j++) {
            // cout << "i: " << i << " j: " << j << endl;
            if (!litsSD[j]) {
              continue;
            }
            if (!matches[i][j]) {
              continue;
            }
            // debug << "match cached" << endl;
            ALWAYS(MatchingUtils::match((*premise)[i], (*cl)[j], false, binder));
            // debug << "matched" << endl;
            BacktrackData localBD;
            {
              TIME_TRACE("copy subst");
              auto it = newSubst.iterator();
              while (it.hasNext()) {
                unsigned v;
                TermList t;
                it.next(v,t);
                TermList temp;
                if (subst.findBinding(v,temp)) {
                  if (temp!=t) {
                    goto nomatch;
                  }
                } else {
                  subst.bind(v,t);
                  localBD.addBacktrackObject(new BindingBO(subst, v));
                }
              }
            }
            // debug << "subst copied " << subst << endl;
            // check arrays
            {
              TIME_TRACE("check arrays");
              bool anyLeft = false;
              for (unsigned k = 0; k < lenSR; k++) {
                if (i == k || !litsSR[k]) {
                  continue;
                }
                anyLeft = true;
                if (!GorGEorIC(premiseLo,i,k)) {
                  goto nomatch;
                }
              }
              if (!anyLeft) {
                // subsumption
                env.statistics->newForwardSubsumed++;
                if (!checkSubsumption(cl, premise)) {
                  cout << "wrong subsumption " << *cl << endl 
                        << "by                " << *premise << endl;
                }
                return true;
              }
              unsetBoolBacktrack(localBD,litsSR,i);
              unsetBoolBacktrack(localBD,litsSD,j);
              for (unsigned l = 0; l < lenSR; l++) {
                if (i == l) {
                  continue;
                }
                if (matches[l][j]) {
                  unsetBoolBacktrack(localBD,matches[l],j);
                  auto v = matchesSetBits[l]--;
                  localBD.addBacktrackObject(new ValueSetBO<unsigned>(matchesSetBits[l], v));
                  if (v == 1) {
                    TIME_TRACE("no matches left filter");
                    goto nomatch;
                  }
                }
              }

              anyLeft = false;
              for (unsigned k = 0; k < clen; k++) {
                if (j == k || !litsSD[k]) {
                  continue;
                }
                if (GorGEorIC(clLo,j,k)) {
                  anyLeft = true;
                  continue;
                }
                unsetBoolBacktrack(localBD,litsSD,k);
                for (unsigned l = 0; l < lenSR; l++) {
                  if (matches[l][k]) {
                    unsetBoolBacktrack(localBD,matches[l],k);
                    auto v = matchesSetBits[l]--;
                    localBD.addBacktrackObject(new ValueSetBO<unsigned>(matchesSetBits[l], v));
                    if (v == 1) {
                      TIME_TRACE("no matches left filter");
                      goto nomatch;
                    }
                  }
                }
              }
              if (!anyLeft) {
                goto nomatch;
              }
            }
            found = true;
            localBD.addBacktrackObject(new ValueSetBO<unsigned>(iSR,i));
            localBD.addBacktrackObject(new ValueSetBO<unsigned>(iSD,j+1));
            iSR = 0;
            iSD = 0;
            bds.push(localBD);
            goto fin;

          nomatch:
            ASS(!found);
            localBD.backtrack();
          }
        }

      fin:
        if (!found) {
          if (bds.isEmpty()) {
            goto fail;
          }
          // otherwise backtrack
          TIME_TRACE("backtrack");
          auto bd = bds.pop();
          bd.backtrack();
          continue;
        }
      }

    fail:
      // if (checkSubsumption(cl, premise)) {
      //   cout << "should be subsumed " << *cl << endl 
      //        << "by                " << *premise << endl;
      //   cout << debug.str() << endl;
      //   throw UserErrorException();
      // }
      while (bds.isNonEmpty()) {
        bds.pop().drop();
      }
      continue;
    }
  }
  return false;
}

} // namespace Inferences
