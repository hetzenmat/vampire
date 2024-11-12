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
 * @file WHNFDeref.hpp
 */

#ifndef __WHNFDeref__
#define __WHNFDeref__

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/TermTransformer.hpp"

using namespace Kernel;

// similar to BetaNormaliser, but places a term in WHNF instead
// of into full normal form
class WHNFDeref : public TermTransformer
{
public:

  WHNFDeref(RobSubstitution* sub) : _sub(sub) {
    dontTransformSorts();
  }
  TermSpec normalise(TermSpec t);
  // puts term into weak head normal form
  TermList transformSubterm(TermList t) override;
  bool exploreSubterms(TermList orig, TermList newTerm) override;

private:
  int _index;
  RobSubstitution* _sub;
};



#endif // __WHNFDeref__
