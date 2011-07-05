/**
 * @file TrivialPredicateRemover.cpp
 * Implements class TrivialPredicateRemover.
 */

#include "Lib/ArrayMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "PredicateDefinition.hpp"
#include "Statistics.hpp"

#include "TrivialPredicateRemover.hpp"


#undef LOGGING
#define LOGGING 0

namespace Shell
{

void TrivialPredicateRemover::apply(UnitList*& units)
{
  CALL("TrivialPredicateRemover::apply");

  TimeCounter tc(TC_TRIVIAL_PREDICATE_REMOVAL);

  scan(units);

  UnitList::DelIterator dit(units);
  while(dit.hasNext()) {
    Clause* cl = static_cast<Clause*>(dit.next());
    if(_removed.contains(cl)) {
      dit.del();
    }
  }
}

void TrivialPredicateRemover::scan(UnitList* units)
{
  CALL("TrivialPredicateRemover::scan");

  unsigned preds = env.signature->predicates();
  _posOcc.init(preds, 0);
  _negOcc.init(preds, 0);
  _predClauses.ensure(preds);


  for(unsigned i=0; i<preds; i++) {
    if(PredicateDefinition::isBuiltIn(i)) {
      //we add a fictional positive and negative occurrence to interpreted
      //predicates, so that they are not considered trivial
      _posOcc[i]++;
      _negOcc[i]++;
    }
  }

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    ASS(u->isClause());
    Clause* cl = static_cast<Clause*>(u);
    count(cl, 1);
  }

  Stack<unsigned> toDo;

  for(unsigned i=0; i<preds; i++) {
    if(_posOcc[i]==0 || _negOcc[i]==0) {
      toDo.push(i);
    }
  }

  ASS(_reachedZeroes.isEmpty());

  while(toDo.isNonEmpty()) {
    unsigned removedPred = toDo.pop();
    ClauseSet::Iterator cit(_predClauses[removedPred]);
    while(cit.hasNext()) {
      Clause* cl = cit.next();
      if(_removed.contains(cl)) {
	continue;
      }
      _removed.insert(cl);
      count(cl, -1);
      env.statistics->trivialPredicates++;
      LOG("Removed due to trivial predicate: " << cl->toString());
    }
    while(_reachedZeroes.isNonEmpty()) {
      unsigned zpred = _reachedZeroes.pop();
      if(zpred!=removedPred) {
	toDo.push(zpred);
      }
    }
  }
}

/**
 * Update predicate occurrence counters with clause @c cl.
 *
 * If we're decreasing counters and a counter reaches zero,
 * its predicate number is added to the @c _reachedZeroes stack.
 */
void TrivialPredicateRemover::count(Clause* cl, int add)
{
  CALL("TrivialPredicateRemover::count");

  //1 - positive, -1 - negative, 0 - both occurrences
  static ArrayMap<int> predOccurrences;
  predOccurrences.ensure(env.signature->predicates());
  predOccurrences.reset();

  static Stack<unsigned> preds;
  preds.reset();

  Clause::Iterator it(*cl);
  while(it.hasNext()) {
    Literal* lit = it.next();
    unsigned pred = lit->functor();
    int val = lit->isPositive() ? 1 : -1;
    if(predOccurrences.find(pred)) {
      if(val!=predOccurrences.get(pred)) {
	predOccurrences.set(pred, 0);
      }
    }
    else {
      predOccurrences.set(pred, val);
      preds.push(pred);
      _predClauses[pred].insert(cl);
    }
  }

  Stack<unsigned>::Iterator pit(preds);
  while(pit.hasNext()) {
    unsigned pred = pit.next();
    int val = predOccurrences.get(pred);
    if(val==0) {
      continue;
    }
    ASS(val==1 || val==-1);
    int& updatedCtr = (val==1) ? _posOcc[pred] : _negOcc[pred];
    if(add<0) {
      ASS_GE(updatedCtr,-add);
      if(updatedCtr==-add) {
	_reachedZeroes.push(pred);
      }
    }
    updatedCtr += add;
  }
}

}
