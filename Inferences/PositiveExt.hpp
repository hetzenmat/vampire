/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef VAMPIRE_INFERENCES_POSITIVEEXT
#define VAMPIRE_INFERENCES_POSITIVEEXT

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Shell/Options.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class PositiveExt
    : public GeneratingInferenceEngine {
public:
  ClauseIterator generateClauses(Clause *premise) override;

private:
  struct ResultFn;
  struct IsPositiveEqualityFn;
};
} // namespace Inferences

#endif // VAMPIRE_INFERENCES_POSITIVEEXT
