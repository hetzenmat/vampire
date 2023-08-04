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
 * @file Demodulation.hpp
 * Defines class Demodulation
 *
 */

#ifndef __Demodulation__
#define __Demodulation__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardDemodulationNew
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(ForwardDemodulationNew);
  USE_ALLOCATOR(ForwardDemodulationNew);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  VirtualIterator<pair<Clause*,ClauseIterator>> perform(Clause* cl) override = 0;
protected:
  bool _preorderedOnly;
  bool _redundancyCheck;
  bool _encompassing;
  DemodulationLHSIndex* _index;
  DHMap<Term*,pair<TermList,bool>> _normalForms;
};

template <bool combinatorySupSupport>
class ForwardDemodulationImplNew
: public ForwardDemodulationNew
{
public:
  CLASS_NAME(ForwardDemodulationImplNew);
  USE_ALLOCATOR(ForwardDemodulationImplNew);

  VirtualIterator<pair<Clause*,ClauseIterator>> perform(Clause* cl) override;
private:
  bool forwardSimplifyingLoop(LiteralStack& lits, bool eqTaut, Clause*& premise);
};

};

#endif /*__Demodulation__*/
