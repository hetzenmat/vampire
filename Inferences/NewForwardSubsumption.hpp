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
 * @file NewForwardSubsumption.hpp
 * Defines class NewForwardSubsumption.
 */


#ifndef __NewForwardSubsumption__
#define __NewForwardSubsumption__


#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class NewForwardSubsumption
: public ForwardSimplificationEngine
{
public:
  CLASS_NAME(NewForwardSubsumption);
  USE_ALLOCATOR(NewForwardSubsumption);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

private:
  MaximalLiteralForwardSubsumptionIndex* _index;
};


};

#endif /* __NewForwardSubsumption__ */
