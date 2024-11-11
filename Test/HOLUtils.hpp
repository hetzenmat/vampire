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
 * @file HOLUtils.hpp
 */

#ifndef __HOLUtils__
#define __HOLUtils__


#include "Kernel/TypedTermList.hpp"

#define DECL_CONST(name, sort) \
  unsigned name ## Index = env.signature->addFunction(#name, 0); \
  env.signature->getFunction(name ## Index)->setType(OperatorType::getFunctionType({}, sort)); \
  TypedTermList name = TypedTermList(TermList(Term::createConstant(name ## Index)), sort);

#define DECL_VAR(name, index, sort) \
  TypedTermList name = TypedTermList(TermList::var(index), sort);

namespace HOLUtils {

using Kernel::TypedTermList;

TypedTermList AP(TypedTermList lhs, TypedTermList rhs);
TypedTermList AP_l(std::initializer_list<TypedTermList> terms);
TypedTermList LAM(TypedTermList var, TypedTermList term);
TypedTermList toDeBruijnIndices(TypedTermList t);
}



#endif // __HOLUtils__
