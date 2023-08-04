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
 * @file ForwardDemodulation.hpp
 * Defines class ForwardDemodulation
 *
 */

#ifndef __ForwardDemodulation__
#define __ForwardDemodulation__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


class NonParallelNonVariableNonTypeIterator
  : public IteratorCore<Term*>
{
public:
  NonParallelNonVariableNonTypeIterator(const NonParallelNonVariableNonTypeIterator&);

  NonParallelNonVariableNonTypeIterator(Literal* term)
  : _stack(8),
    _added(0)
  {
    _stack.push(term);
    NonParallelNonVariableNonTypeIterator::next();
  }

  void reset(Term* term, bool includeSelf=false)
  {
    _stack.reset();
    _added = 0;
    _stack.push(term);
    if (!includeSelf) {
      NonParallelNonVariableNonTypeIterator::next();
    }
  }

  /** true if there exists at least one subterm */
  bool hasNext() { return !_stack.isEmpty(); }
  Term* next();
  void right();
private:
  /** available non-variable subterms */
  Stack<Term*> _stack;
  /** the number of non-variable subterms added at the last iteration, used by right() */
  int _added;
};

class ForwardDemodulation
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(ForwardDemodulation);
  USE_ALLOCATOR(ForwardDemodulation);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  VirtualIterator<pair<Clause*,ClauseIterator>> perform(Clause* cl) override = 0;
protected:
  bool _preorderedOnly;
  bool _redundancyCheck;
  bool _encompassing;
  DemodulationLHSIndex* _index;
  DemodulationSubtermIndex* _bwIndex;
};

template <bool combinatorySupSupport>
class ForwardDemodulationImpl
: public ForwardDemodulation
{
public:
  CLASS_NAME(ForwardDemodulationImpl);
  USE_ALLOCATOR(ForwardDemodulationImpl);

  VirtualIterator<pair<Clause*,ClauseIterator>> perform(Clause* cl) override;
private:
  void perform(TypedTermList trm, Literal* lit, Clause* cl, Stack<pair<Clause*,Clause*>>& resPremisePairs, bool exhaustive);

  DHSet<TermList> _attempted;
};


};

#endif /*__ForwardDemodulation__*/
