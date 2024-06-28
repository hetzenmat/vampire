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
* @file BetaEtaSimplify.hpp
*/


#ifndef __BetaEtaSimplify__
#define __BetaEtaSimplify__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/TermTransformer.hpp"

namespace Inferences {

class BetaEtaSimplify
   : public ImmediateSimplificationEngine
{
public:
 USE_ALLOCATOR(BetaEtaSimplify);

 Clause* simplify(Clause* cl);
};

};

#endif /* __BetaEtaSimplify__ */
