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

#include "Indexing/TermSubstitutionTree.hpp"
#include "Shell/LambdaConversion.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/TestUtils.hpp"




TypedTermList LAM(TypedTermList var, TypedTermList term) {
  
    auto varSort = var.sort();
    auto termSort = term.sort();

    VList* boundVar = new VList(var.var());
    SList* boundVarSort = new SList(varSort);
    Term* lambdaTerm = Term::createLambda(term, boundVar, boundVarSort, termSort);

    return {TermList(lambdaTerm), TermList(AtomicSort::arrowSort(varSort, termSort))};
}

void require(bool v) {
  if (!v) {
    throw std::exception();
  }
}

TypedTermList AP(TypedTermList lhs, TypedTermList rhs) {
  require(lhs.sort().isArrowSort());

  auto [domain, result] = lhs.sort().asPair();
  
  if (domain != rhs.sort()) {
    std::cout << lhs << " @ " << rhs << std::endl;
  }

  ASS(domain == rhs.sort());

  return {ApplicativeHelper::app(lhs.sort(), lhs, rhs), result};
}

TypedTermList AP_l(std::initializer_list<TypedTermList> terms) {
  auto size = terms.size();

  ASS(size > 0);
  auto a = std::data(terms);
  TypedTermList res = a[0];
  
  for (std::size_t i = 0; i + 1 < size; ++i) {
    res = AP(res, a[i+1]);
  }

  return res;
}

TypedTermList toDeBruijnIndices(TypedTermList t) {
  return {LambdaConversion::convertLambda(t), t.sort()};
}

#define DECL_ATOMIC_SORT(name) TermList name = TermList(AtomicSort::createConstant(#name));

#define DECL_ARROW_SORT(name, from, to) TermList name = TermList(AtomicSort::arrowSort(from, to));

#define DECL_VAR(name, index, sort) [[maybe_unused]] TypedTermList name = TypedTermList(TermList::var(index), sort);

#define DECL_CONST(name, sort) \
  unsigned name ## Index = env.signature->addFunction(#name, 0); \
  env.signature->getFunction(name ## Index)->setType(OperatorType::getFunctionType({}, sort)); \
  [[maybe_unused]] TypedTermList name = TypedTermList(TermList(Term::createConstant(name ## Index)), sort);

#define BRACED_INIT_LIST(...) {__VA_ARGS__}

#define RUN_MATCH_TEST(NAME, INDEXED, QUERY, EXPECTED) \
  TEST_FUN(NAME) { \
    env.options->setHolPrinting(Options::HPrinting::DB_INDICES); \
    auto index = TermSubstitutionTree<TermWithoutValue>(); \
    \
    DECL_ATOMIC_SORT(srt) \
    DECL_ARROW_SORT(fSrt, srt, srt) \
    DECL_ARROW_SORT(kSrt, srt, fSrt) \
    \
    DECL_VAR(x0, 0, srt) \
    DECL_VAR(y0, 3, srt) \
    DECL_VAR(x1, 1, srt) \
    DECL_VAR(x2, 2, fSrt) \
    \
    DECL_CONST(k, kSrt)\
    DECL_CONST(f, fSrt)\
    DECL_CONST(g, fSrt)\
    DECL_CONST(a, srt) \
    DECL_CONST(b, srt) \
    DECL_CONST(c, srt) \
    \
    for (auto t : BRACED_INIT_LIST INDEXED) index.insert(TermWithoutValue(toDeBruijnIndices(t))); \
    \
    auto query = toDeBruijnIndices(QUERY);\
    auto it = iterTraits(index.getHOLInstances(query)); \
    \
    std::vector<TypedTermList> is {}; \
    for (auto qr : it) is.push_back(qr.data->term); \
    \
    std::vector<TypedTermList> expected {}; \
    for (TypedTermList t : std::initializer_list<TypedTermList>BRACED_INIT_LIST EXPECTED) expected.push_back(toDeBruijnIndices(t)); \
    \
    if (Test::TestUtils::permEq(is, expected, [](auto& l, auto& r) { return l == r; })) { \
      std::cout << "[  OK  ] " << std::endl; \
    } else { \
      std::cout << "[ FAIL ]\nExpected:"; \
      for (auto i : expected) std::cout << "\n" << i; \
      std::cout << "\nResult:"; \
      for (auto i : is) std::cout << "\n" << i; \
      std::cout << std::endl; \
      exit(-1); \
    } \
}


RUN_MATCH_TEST(
/* name */     hol_matching_01,
/* indexed */  ( LAM(x1, AP(f, x1)) ), 
/* query*/     x2,
/* expected */ ( LAM(x1, AP(f, x1)) )
) 

RUN_MATCH_TEST(
/* name */     hol_matching_02,
/* indexed */  ( AP(AP(k, AP(g, a)), AP(g, a))
               , AP(AP(k, AP(g, c)), AP(g, b))
               , AP(AP(k, x1), x1) ), 
/* query*/     AP(AP(k, x0), x0),
/* expected */ ( AP(AP(k, AP(g, a)), AP(g,a))
               , AP(AP(k, x1), x1) )
)

RUN_MATCH_TEST(
/* name */     hol_matching_03,
/* indexed */  ( LAM(x0, AP_l({k, AP(f, x0), a})) ), 
/* query*/     LAM(x0, AP_l({k, x1, a})),
/* expected */ (  )
) 

RUN_MATCH_TEST(
/* name */     hol_matching_04,
/* indexed */  ( LAM(x0, AP_l({k, AP(f, x1), a}))
               , LAM(x0, AP_l({k, x1, a})) ), 
/* query*/     LAM(x0, AP_l({k, x0, a})),
/* expected */ (  )
) 

RUN_MATCH_TEST(
/* name */     hol_matching_05,
/* indexed */  ( LAM(x0, LAM(x1, x0)) ), 
/* query*/     LAM(x0, LAM(x1, y0)),
/* expected */ (  )
) 

RUN_MATCH_TEST(
/* name */     hol_matching_06,
/* indexed */  ( AP_l({k, a, b})
               , AP_l({k, b, b})
               ), 
/* query*/     AP_l({k, x0, x0}),
/* expected */ ( AP_l({k, b, b}) )
) 

RUN_MATCH_TEST(
/* name */     hol_matching_07,
/* indexed */  ( AP_l({k, a, b}) ), 
/* query*/     AP_l({k, AP(f, x0), x0}),
/* expected */ (  )
) 

#undef BRACED_INIT_LIST
#undef RUN_MATCH_TEST
#undef DECL_ATOMIC_SORT
#undef DECL_ARROW_SORT
#undef DECL_VAR
#undef DECL_CONST
