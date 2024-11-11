/*
* This file is part of the source code of the software program
 * Vampire. It is protected by APplicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**!
 *
 * @author Matthias Hetzenberger
 */

#include "Kernel/HOLUnification.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Shell/LambdaConversion.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/TestUtils.hpp"
#include "Test/HOLUtils.hpp"

using namespace HOLUtils;


TEST_FUN(unif1) {
  Problem prb;
  prb.forceHigherOrder();
  env.setMainProblem(&prb);

  TermSubstitutionTree<TermWithoutValue> index(SplittingAlgo::HOL_UNIF);

  auto srt = TermList(AtomicSort::createConstant("srt"));
  auto srtSrt = TermList(AtomicSort::arrowSort(srt, srt));

  auto x1 = TypedTermList(TermList::var(1), srt);

  unsigned fIndex = env.signature->addFunction("f", 0); \
  env.signature->getFunction(fIndex)->setType(OperatorType::getFunctionType({}, srtSrt)); \
  auto f = TypedTermList(TermList(Term::createConstant(fIndex)), srtSrt);


  unsigned cIndex = env.signature->addFunction("c", 0); \
  env.signature->getFunction(cIndex)->setType(OperatorType::getFunctionType({}, srt)); \
  auto c = TypedTermList(TermList(Term::createConstant(cIndex)), srt);

  const std::initializer_list terms = {x1, f, c, AP(f, c), AP(f, x1), AP(f, AP(f, c))};
  for (const auto term : terms) {
    index.insert(TermWithoutValue(term));
  }

  std::cout << multiline(index) << std::endl;
}

TEST_FUN(unif2) {
  Problem prb;
  prb.forceHigherOrder();

  env.setMainProblem(&prb);
  env.options->set("hol_unif_depth", "2");

  // example of paper "A Higher-Order Vampire (Short Paper)"
  // unification problem: x a b =?= f b a
  // a, b : srt
  // x, f : srt > srt > srt

  auto srt = TermList(AtomicSort::createConstant("srt"));
  auto funcSrt = TermList(AtomicSort::arrowSort(srt, srt));
  auto fSrt = TermList(AtomicSort::arrowSort(srt, funcSrt));

  DECL_CONST(f, fSrt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_VAR(x, 0, fSrt);

  auto lhs = AP(AP(x, a), b);
  auto rhs = AP(AP(f, b), a);

  auto unif = new UnificationAlgorithms::HigherOrderUnifiersItWrapper({static_cast<TermList>(lhs), QUERY_BANK}, lhs.sort(), {static_cast<TermList>(rhs), RESULT_BANK}, rhs.sort(), false);

}