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
 * @file UnitEqualityReduction.hpp
 * Defines class UnitEqualityReduction
 *
 */

#ifndef __UnitEqualityReduction__
#define __UnitEqualityReduction__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class ForwardUnitEqualityReduction
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(ForwardUnitEqualityReduction);
  USE_ALLOCATOR(ForwardUnitEqualityReduction);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  VirtualIterator<pair<Clause*,ClauseIterator>> perform(Clause* cl) override;
protected:
  DemodulationLHSIndex* _lhsIndex;
  RewritingRHSIndex* _rhsIndex;
};

class BackwardUnitEqualityReduction
: public BackwardSimplificationEngine
{
public:
  CLASS_NAME(BackwardUnitEqualityReduction);
  USE_ALLOCATOR(BackwardUnitEqualityReduction);

  void attach(SaturationAlgorithm* salg);
  void detach();

  void perform(Clause* premise, BwSimplificationRecordIterator& simplifications);
private:
  DemodulationSubtermIndex* _index;
  DemodulationLHSIndex* _lhsIndex;
};

};

#endif /*__UnitEqualityReduction__*/
