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
 * @file PrimitiveInstantiation.hpp
 * Defines class PrimitiveInstantiation.
 */


#ifndef __PrimitiveInstantiation__
#define __PrimitiveInstantiation__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class PrimitiveInstantiation
: public GeneratingInferenceEngine
{
public:
  USE_ALLOCATOR(PrimitiveInstantiation);

  ClauseIterator generateClauses(Clause* premise) override;
  
private:
  struct ResultFn;
  struct IsInstantiable;
};


};

#endif /* __PrimitiveInstantiation__ */
