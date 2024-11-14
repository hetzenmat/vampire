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

#include <Kernel/HOL/ToPlaceholders.hpp>

using namespace HOLUtils;

// x a b =?= f b a
// x, f : srt > srt > srt
// a, b : srt

TEST_FUN(unif1) {
  Problem prb;
  prb.forceHigherOrder();
  env.setMainProblem(&prb);

  TermSubstitutionTree<TermWithValue<TermList>> index(SplittingAlgo::HOL_UNIF);
  index.setPreprocessor([](TermWithValue<TermList>* t) {
    LOG("preprocess before", t->term.toString());
    auto skeleton = TypedTermList(ToPlaceholders().replace(t->term), t->term.sort());
    t->term = skeleton;
    t->value = static_cast<TermList>(t->term);
    LOG("preprocess after", t->term.toString());

    // sort(t->value) == t->term.sort()
  });

  // if(env.getMainProblem()->isHigherOrder() && _algo == SplittingAlgo::HOL_UNIF) {
  //   // replace higher-order terms with placeholder constants
  //   //tt = TypedTermList(ToPlaceholders().replace(tt), tt.sort());
  //   THROW_MH("");
  // }

  auto srt = TermList(AtomicSort::createConstant("srt"));
  auto srtSrt = TermList(AtomicSort::arrowSort(srt, srt));
  auto fSrt = TermList(AtomicSort::arrowSort(srt, srt, srt));

  DECL_VAR(x, 0, fSrt)
  DECL_CONST(f, fSrt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto xab = AP_l({x, a, b});
  index.insert(TermWithValue(xab, static_cast<TermList>(xab)));

  std::cout << multiline(index) << std::endl;

  auto fba = AP_l({f, b, a});

  auto i = iterTraits(index.getHOLUnifiers(fba, true));
  for (const auto& result : i) {
    std::cout << result << std::endl;
  }
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