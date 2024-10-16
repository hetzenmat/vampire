/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Forwards.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Test/TestUtils.hpp"
#include "Test/SubstituionTreeSugar.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

using namespace std;
using namespace Kernel;
using namespace Indexing;
using namespace Test;

using Data = int;
using LeafData = TermWithValue<Data>;

using STree = SubstitutionTree<LeafData>;
using QRes = QueryRes<ResultSubstitutionSP, LeafData>;

struct Expected {
  Data data;

  bool matches(QRes const& r) 
  { return r.data->value == data; }

  friend std::ostream& operator<<(std::ostream& out, Expected const& self)
  { return out << self.data; }
};

struct FirstOrderUnification {
  auto find(STree& tree, TermList query) {
    return iterTraits(tree.iterator<STree::Iterator<RetrievalAlgorithms::RobUnification>>(query, /*retrieveSubstitutions=*/ true, /*reversed=*/false));
  }
};

struct HigherOrderUnification {
  auto find(STree& tree, TermList query) {
    return iterTraits(tree.iterator<STree::Iterator<RetrievalAlgorithms::HOLUnification>>(query, /*retrieveSubstitutions=*/ true, /*reversed=*/false));
  }
};


template<class Retrieval>
struct SubsTreeTest {
  STree tree;
  TermList query;
  Stack<Expected> expected;
  Retrieval retrieval;

  void run() {

    auto resultIter = retrieval.find(tree, query);
    auto missing = expected;
    Stack<LeafData const*> unexpected;
    Stack<LeafData const*> results;
    for (auto res : resultIter) {
      auto idx = arrayIter(missing).findPosition([&](auto& exp) { return exp.matches(res); });
      results.push(res.data);
      if (idx.isNone()) {
        unexpected.push(res.data);
      } else {
        missing.swapRemove(*idx);
      }
    }
    std::cout << "[     tree ] " << multiline(tree) << std::endl;
    std::cout << "[    query ] " << pretty(query) << std::endl;
    std::cout << "[ expected ] " << pretty(expected) << std::endl;
    std::cout << "[  results ] " << pretty(results) << std::endl;
    if (missing.isEmpty() && unexpected.isEmpty()) {
      std::cout << "[ OK ] " << std::endl;
    } else {
      std::cout << "[ FAIL ] " << std::endl;
      std::cout << "[ unexpected ] " << pretty(unexpected) << std::endl;
      std::cout << "[    missing ] " << pretty(missing) << std::endl;
      ASSERTION_VIOLATION
    }
  }
};

#define TEST_SUGAR                                                                        \
    DECL_DEFAULT_VARS                                                                   \
    DECL_VAR(x0, 0)                                                                     \
    DECL_VAR(x1, 1)                                                                     \
    DECL_VAR(x2, 2)                                                                     \
    DECL_VAR(x3, 3)                                                                     \
    DECL_SORT(alpha)                                                                    \
    DECL_CONST(a, alpha)                                                               \
    DECL_CONST(b, alpha)                                                               \
    DECL_CONST(c, alpha)                                                               \
    DECL_FUNC(f, {alpha}, alpha)                                                               \
    DECL_FUNC(g, {alpha}, alpha)                                                               \
    DECL_FUNC(h, {alpha}, alpha)                                                               \
    DECL_FUNC(f2, {alpha, alpha}, alpha)                                                               \
 

#define RUN_TEST(name, sugar, ...)                                                        \
  TEST_FUN(name) {                                                                        \
       __ALLOW_UNUSED(sugar)                                                              \
       __VA_ARGS__.run();                                                                 \
  }                                                                                       \

using namespace SubsTreeBuilder;

RUN_TEST(tree_test_01,
    TEST_SUGAR,
    SubsTreeTest<FirstOrderUnification> {
      .tree = subsTree(0, { 
          leaf(TermList(f(a)), { termWithValue(f(a), 0), }),
          leaf(TermList(g(b)), { termWithValue(g(b), 1), }),
      }),
      .query = x,
      .expected = { { .data = 0 },{ .data = 1 }, },
    })

RUN_TEST(tree_test_02,
    TEST_SUGAR,
    SubsTreeTest<FirstOrderUnification> {
      .tree = subsTree(0, { 
          internal(g(S(1)), 1, {
            leaf(TermList(a), { termWithValue(f(a), 0), }),
            leaf(TermList(b), { termWithValue(f(b), 1), }),
          }),
          internal(f(S(1)), 1, {
            leaf(TermList(a), { termWithValue(f(a), 0), }),
            leaf(TermList(b), { termWithValue(f(b), 1), }),
          })
      }),
      .query = f(x),
      .expected = { { .data = 0 },{ .data = 1 }, },
    })


RUN_TEST(tree_test_03,
    TEST_SUGAR,
    SubsTreeTest<FirstOrderUnification> {
      .tree = subsTree(0, { 
          internal(f2(S(1), a), 1, {
            leaf(TermList(a), { termWithValue(f(a), 0), }),
            leaf(TermList(b), { termWithValue(f(b), 1), }),
          }),
          internal(f(S(1)), 1, {
            leaf(TermList(a), { termWithValue(f(a), 2), }),
          })
      }),
      .query = f2(x, x),
      .expected = { { .data = 0 }, },
    })

RUN_TEST(tree_test_04,
    TEST_SUGAR,
    SubsTreeTest<FirstOrderUnification> {
      .tree = subsTree(0, { 
          leaf(TermList(a), { termWithValue(a, 1), }),
          internal(f2(S(1), a), 1, {
            leaf(TermList(a), { termWithValue(f(a), 0), }),
            leaf(TermList(y), { termWithValue(f(y), 1), }),
          }),
          internal(f(S(1)), 1, {
            leaf(TermList(a), { termWithValue(f(a), 2), }),
          })
      }),
      .query = f2(x, x),
      .expected = { { .data = 0 },  { .data = 1 }, },
    })

RUN_TEST(tree_test_05,
    TEST_SUGAR,
    SubsTreeTest<FirstOrderUnification> {
      .tree = subsTree(0, { 
          leaf(TermList(a), { termWithValue(a, 1), }),
          internal(f2(S(1), a), 1, {
            leaf(TermList(y), { termWithValue(f(y), 1), }),
          }),
          internal(f(S(1)), 1, {
            leaf(TermList(a), { termWithValue(f(a), 2), }),
          })
      }),
      .query = f2(x, x),
      .expected = { { .data = 1 }, },
    })

// TODO matthias: write test cases with HigherOrderUnification
