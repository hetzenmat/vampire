//
// Created by matt on 24.10.24.
//

#include "HOLUtils.hpp"

#include "Kernel/HOL/ApplicativeHelper.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Shell/LambdaConversion.hpp"

namespace HOLUtils {

using Kernel::TypedTermList;

TypedTermList AP(TypedTermList lhs, TypedTermList rhs) {
  ASS(lhs.sort().isArrowSort())

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

TypedTermList LAM(TypedTermList var, TypedTermList term) {

  auto varSort = var.sort();
  auto termSort = term.sort();

  VList* boundVar = new VList(var.var());
  SList* boundVarSort = new SList(varSort);
  Term* lambdaTerm = Term::createLambda(term, boundVar, boundVarSort, termSort);

  return {TermList(lambdaTerm), TermList(AtomicSort::arrowSort(varSort, termSort))};
}

TypedTermList toDeBruijnIndices(TypedTermList t) {
  return {LambdaConversion::convertLambda(t), t.sort()};
}

}