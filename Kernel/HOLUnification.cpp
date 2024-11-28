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
* @file HOLUnification.cpp
* Defines class HOLUnification.
*/

#include "HOLUnification.hpp"

namespace Kernel::UnificationAlgorithms {

OracleResult fixpointUnify(TermSpec var, TermSpec t, RobSubstitution* sub) {

  // var can be an eta expanded var due to the normalisation of lambda prefixes

  auto res = var.term.isEtaExpandedVar();
  if (res.isNone())
    return OracleResult::OUT_OF_FRAGMENT;
  var = TermSpec(res.unwrap(), var.index);

  struct TermListFP {
    TermSpec t;
    bool underFlex;
    unsigned depth;
  };

  bool tIsLambda = t.term.whnfDeref(sub, t.index).isLambdaTerm();

  return OracleResult::SUCCESS;
}

}