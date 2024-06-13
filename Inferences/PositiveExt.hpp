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
* @file PositiveExt.hpp
* Defines class positive extensionality.
*/


#ifndef __PositiveExt__
#define __PositiveExt__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Shell/Options.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class PositiveExt
   : public GeneratingInferenceEngine
{
public:
 USE_ALLOCATOR(PositiveExt);

 ClauseIterator generateClauses(Clause* premise);
private:
 struct ResultFn;
 struct IsPositiveEqualityFn;
};


};

#endif /* __PositiveExt__ */
