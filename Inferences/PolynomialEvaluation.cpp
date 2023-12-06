/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/QKbo.hpp"
#include "Lib/Metaiterators.hpp"
#include "Shell/Statistics.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"

#define DEBUG(...)  // DBG(__VA_ARGS__)
using namespace Lib;


namespace Inferences {

using LitSimplResult = SimplifyingGeneratingLiteralSimplification::Result;

PolynomialEvaluationRule::~PolynomialEvaluationRule() {}


PolynomialEvaluationRule::PolynomialEvaluationRule(Ordering& ordering) 
  : SimplifyingGeneratingLiteralSimplification(InferenceRule::EVALUATION, ordering)
  // TODO we have an additional step of normalization here. simplify!
  , _inner(/* removeZeros */ true) 
  , _alwaysEvaluate(env.options->lasca())
  {}


Literal* createLiteral(Literal* orig, PolyNf* evaluatedArgs) {
  CALL("createLiteral");

  if (orig->isEquality()) {
    return Literal::createEquality(
          orig->polarity(), 
          evaluatedArgs[0].denormalize(), 
          evaluatedArgs[1].denormalize(), 
          SortHelper::getTermArgSort(orig, 0));
  } else {
    auto termArgs = orig->numTermArguments();
    auto typeArgs = orig->numTypeArguments();
    Stack<TermList> args(typeArgs + termArgs);
    for (unsigned i = 0; i < typeArgs; i++) {
      args.push(orig->typeArg(i));
    }
    for (unsigned i = 0; i < termArgs; i++) {
      args.push(evaluatedArgs[i].denormalize());
    }
    return Literal::create(orig, args.begin());
  }
}

PolynomialEvaluationRule::Result PolynomialEvaluationRule::simplifyLiteral(Literal* lit) 
{
  CALL("PolynomialEvaluation::simplifyLiteral");
  TIME_TRACE("polynomial evaluation");

  Stack<PolyNf> terms(lit->numTermArguments());
  auto anyChange = false;
  for (unsigned i = 0; i < lit->numTermArguments(); i++) {
    auto term = lit->termArg(i);
    auto norm = PolyNf::normalize(TypedTermList(term, SortHelper::getTermArgSort(lit, i)));
    // auto ev = _inner.evaluate(norm);
    anyChange = anyChange || norm.denormalize() != term;
    terms.push(norm);
  }
  auto simplified = _inner.tryEvalPredicate(lit, terms.begin());
  anyChange = anyChange || simplified.isSome();

  return anyChange || _alwaysEvaluate
      ? std::move(simplified)
        .unwrapOrElse([&]()
          { return LitSimplResult::literal(createLiteral(lit, terms.begin())); })
      : LitSimplResult::literal(lit);
}

#include "Kernel/PolynomialNormalizer/PredicateEvaluator.hpp"

Option<LitSimplResult> PolynomialEvaluation::tryEvalPredicate(Literal* orig, PolyNf* evaluatedArgs) const {
  CALL("PolynomialEvaluation::tryEvalPredicate(Literal* term)")
  DEBUG("evaluating: ", orig->toString());

#define HANDLE_CASE(INTER) case Interpretation::INTER: return PredicateEvaluator<Interpretation::INTER>::evaluate(orig, evaluatedArgs); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return Option<LitSimplResult>();
#define HANDLE_NUM_CASES(NUM)                                                                                 \
      HANDLE_CASE(NUM ## _IS_INT)                                                                             \
      HANDLE_CASE(NUM ## _IS_RAT)                                                                             \
      HANDLE_CASE(NUM ## _IS_REAL)                                                                            \
      HANDLE_CASE(NUM ## _GREATER)                                                                            \
      HANDLE_CASE(NUM ## _GREATER_EQUAL)                                                                      \
      HANDLE_CASE(NUM ## _LESS)                                                                               \
      HANDLE_CASE(NUM ## _LESS_EQUAL) 

  auto sym = env.signature->getPredicate(orig->functor());
  if (sym->interpreted()) {
    auto inter = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();

    switch (inter) {
      /* polymorphic */
      HANDLE_CASE(EQUAL)

      /* common number predicates */
      HANDLE_NUM_CASES(INT)
      HANDLE_NUM_CASES(RAT)
      HANDLE_NUM_CASES(REAL)

      /* integer predicates */
      HANDLE_CASE(INT_DIVIDES)
      case Interpretation::ARRAY_BOOL_SELECT:
        return Option<LitSimplResult>();

      case ANY_INTERPRETED_FUNCTION: 
      case Kernel::Theory::INVALID_INTERPRETATION: 
        ASSERTION_VIOLATION_REP(inter)
    }
    WARN("unexpected interpreted predicate: ", *orig, " (inter: ", inter, ")")
    ASSERTION_VIOLATION
    return Option<LitSimplResult>();
  } else {
    return Option<LitSimplResult>();
  }

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}

#include "Inferences/FunctionEvaluation.cpp"

Option<PolyNf> trySimplify(Theory::Interpretation i, PolyNf* evalArgs) 
{
  CALL("trySimplify(Theory::Interpretation i, PolyNf* evalArgs) ")
  try {
    switch (i) {

#define CONSTANT_CASE_2(Num, func, expr)                                                                      \
      case Num##Traits:: func ## I:                                                                           \
        {                                                                                                     \
          using Const = typename Num##Traits::ConstantType;                                                   \
          return trySimplifyConst2<Num##Traits>(evalArgs, [](Const l, Const r){ return expr; });              \
        }                                                                                                     \

#define CASE(inter)                                                                                           \
      case inter: return FunctionEvaluator<inter>::simplify(evalArgs);

#define QUOTIENT_REMAINDER_CASES(X)                                                                           \
      CASE(Theory::INT_QUOTIENT_  ## X)                                                                       \
      CASE(Theory::INT_REMAINDER_ ## X)

#define FRAC_CASE(Num)                                                                                        \
      CASE(Num##Traits::divI)

#define NUM_CASE(Num)                                                                                         \
      case Num ## Traits::minusI: return trySimplifyUnaryMinus<Num ## Traits>(evalArgs);

      NUM_CASE(Int)
      NUM_CASE(Rat)
      NUM_CASE(Real)
      QUOTIENT_REMAINDER_CASES(E)
      QUOTIENT_REMAINDER_CASES(T)
      QUOTIENT_REMAINDER_CASES(F)

      FRAC_CASE(Rat)
      FRAC_CASE(Real)

  // TODO evaluate conversion functions
  // TODO evaluate INT_ABS
  // TODO evaluate INT_SUCCESSOR
  // TODO evaluate FRAC_QUOTIENT
  // TODO evaluate FRAC_ROUND
  // TODO evaluate NUM_TO_NUM
  // TODO evaluate NUM_TRUNCATE

#undef NUM_CASE
#undef QUOTIENT_REMAINDER_CASES
#undef CONSTANT_CASE

      default:
        return none<PolyNf>();
    }
  } catch (MachineArithmeticException&) {
    return none<PolyNf>();

  } catch (DivByZeroException&) {
    return none<PolyNf>();
  }
}


// Option<PolyNf> trySimplify(FuncTerm const& orig, Theory::Interpretation i, PolyNf* evalArgs) 
// {
//   CALL("trySimplify(FuncTerm orig, Theory::Interpretation i, PolyNf* evalArgs) ")
//   switch (i) {
//
// #define CONSTANT_CASE_2(Num, func, expr)                                                                      \
//     case Num##Traits:: func ## I:                                                                           \
//       {                                                                                                     \
//         using Const = typename Num##Traits::ConstantType;                                                   \
//         return trySimplifyConst2<Num##Traits>(evalArgs, [](Const l, Const r){ return expr; });              \
//       }                                                                                                     \
//
// #define CASE(inter)                                                                                           \
//     case inter: return FunctionEvaluator<inter>::simplify(evalArgs);
//
// #define QUOTIENT_REMAINDER_CASES(X)                                                                           \
//     CASE(Theory::INT_QUOTIENT_  ## X)                                                                       \
//     CASE(Theory::INT_REMAINDER_ ## X)
//
// #define FRAC_CASE(Num)                                                                                        \
//     CASE(Num##Traits::divI)
//
// #define NUM_CASE(Num)                                                                                         \
//     case Num ## Traits::minusI: return trySimplifyUnaryMinus<Num ## Traits>(evalArgs);
//
//     NUM_CASE(Int)
//     NUM_CASE(Rat)
//     NUM_CASE(Real)
//     QUOTIENT_REMAINDER_CASES(E)
//     QUOTIENT_REMAINDER_CASES(T)
//     QUOTIENT_REMAINDER_CASES(F)
//
//     FRAC_CASE(Rat)
//     FRAC_CASE(Real)
//
// // TODO evaluate conversion functions
// // TODO evaluate INT_ABS
// // TODO evaluate INT_SUCCESSOR
// // TODO evaluate FRAC_QUOTIENT
// // TODO evaluate FRAC_ROUND
// // TODO evaluate NUM_TO_NUM
// // TODO evaluate NUM_TRUNCATE
//
// #undef NUM_CASE
// #undef QUOTIENT_REMAINDER_CASES
// #undef CONSTANT_CASE
//
//     default:
//       return none<PolyNf>();
//   }
// }


// Option<PolyNf> PolynomialEvaluation::evaluate(TermList term, SortId sort) const 
// { return evaluate(TypedTermList(term, sort)); }
//
// Option<PolyNf> PolynomialEvaluation::evaluate(Term* term) const 
// { return evaluate(TypedTermList(term)); }
//
// Option<PolyNf> PolynomialEvaluation::evaluate(TypedTermList term) const 
// { 
//   auto norm = PolyNf::normalize(term);
//   return someIf(norm.denormalize() == term, 
//       [&]() { return norm; });
// }

template<class Number>
Polynom<Number> _simplifyPoly(Polynom<Number> in, PolyNf* simplifiedArgs, bool removeZeros);

template<class Number>
Monom<Number> _simplifyMonom(Monom<Number> const& in, PolyNf* simplifiedArgs, bool removeZeros);

AnyPoly _simplifyPoly(AnyPoly const& p, PolyNf* ts, bool removeZeros)
{ return p.apply([&](auto& p) { return AnyPoly(_simplifyPoly(p, ts, removeZeros)); }); }

// Option<PolyNf> PolynomialEvaluation::evaluate(PolyNf normalized) const 
// {
//   CALL("PolynomialEvaluation::evaluate(TypedTermList term) const")
//   TIME_TRACE("evaluating polynomial")
//
//   DEBUG("evaluating ", normalized)
//   struct Eval 
//   {
//     const PolynomialEvaluation& norm;
//
//     using Result = PolyNf;
//     using Arg    = PolyNf;
//
//     PolyNf operator()(PolyNf orig, PolyNf* ts, unsigned _nTs)
//     { 
//       return orig.match(
//           [&](FuncTerm f)  -> PolyNf
//           { 
//             return f.function().tryInterpret()
//               .andThen( [&](Theory::Interpretation && i)  -> Option<PolyNf>
//                 { return trySimplify(i, ts); })
//               .unwrapOrElse([&]() -> PolyNf
//                 { return PolyNf(FuncTerm(f.function(), ts)); });
//
//           }, 
//
//           [&](Variable v) 
//           { return v; },
//
//           [&](AnyPoly p) 
//           { return _simplifyPoly(p, ts, /* removeZeros = */ true); }
//       );
//     }
//   };
//   static Memo::Hashed<PolyNf, PolyNf> memo;
//   DBGE(normalized)
//   auto out = evaluateBottomUp(normalized, Eval{ *this }, memo);
//   DBGE(out)
//   if (out == normalized) {
//     return Option<PolyNf>();
//   } else {
//     return Option<PolyNf>(out);
//   }
// }

template<class Number>
Polynom<Number> _simplifyPoly(Polynom<Number> in, PolyNf* simplifiedArgs, bool removeZeros)
{ 
  CALL("simplify(Polynom<Number>const&, PolyNf* simplifiedArgs)") 
  TIME_TRACE("simplify(Polynom<Number>const&, PolyNf* simplifiedArgs)") 
  using Monom   = Monom<Number>;
  using Polynom = Polynom<Number>;
  try {

    // first we simplify all the monoms containted in this polynom
    auto offs = 0;
    auto out = in.iterSummands()
      .map([&](auto monom) {
          Monom simpl = _simplifyMonom(monom, &simplifiedArgs[offs], removeZeros);
          DBG(simpl)
          offs += monom.factors.cntFactors();
          return simpl;
      })
      .filter([](auto monom) { return monom.numeral != Number::zeroC(); })
      .flatMap([](auto monom) {
         // j * ( k1 t1 + ... + kn tn ) ==> j k1 t1 + ... + j kn tn
         return ifElseIter(
                monom.factors.tryMonomFactor().isSome()
                      && monom.factors.tryMonomFactor()->power() == 1
                      && monom.factors.tryMonomFactor()->term().asPoly().isSome()
                , [=]() { return monom.factors.tryMonomFactor()->term()
                                   .asPoly()->template downcast<Number>()->iterSummands()
                                   .map([=](auto m) -> Monom { return monom.numeral * m; }); }
                , [=]() { return getSingletonIterator(monom); });
      })
      .template collect<Stack>();

    // then we sort them by their monom, in order to add up the coefficients efficiently
    std::sort(out.begin(), out.end(), 
        [](auto& l, auto& r) { return l.factors < r.factors; });

    // add up the coefficient (in place)
    {
      auto offs = 0;
      for (unsigned i = 0; i < out.size(); i++) { 
        auto monom = out[i];
        auto numeral = monom.numeral;
        auto& factors = monom.factors;
        while ( i + 1 < out.size() && out[i+1].factors == factors ) {
          numeral = numeral + out[i+1].numeral;
          i++;
        }
        if (numeral != Number::zeroC()) 
          out[offs++] = Monom(numeral, std::move(factors));
      }
      out.truncate(offs);
    }

    auto poly = Polynom(std::move(out));
    poly.integrity();
    DBGE(poly)
    return poly;
  } catch (ArithmeticException&) { 
    return in.replaceTerms(simplifiedArgs);
  }
}

template<class Number>
Monom<Number> _simplifyMonom(Monom<Number> const& in, PolyNf* simplifiedArgs, bool removeZeros) 
{ 

  using Numeral      = typename Number::ConstantType;
  using Monom        = Monom<Number>;
  using MonomFactor  = MonomFactor<Number>;
  using MonomFactors = MonomFactors<Number>;

  auto pow = [](Numeral c, int power) -> Numeral {
    ASS(power > 0)
    auto out = c;
    while (--power > 0) {
      out = out * c;
    }
    return out;
  };

  auto offs = 0;
  auto args = in.factors.iter()
    .map([&](auto f) { return MonomFactor(simplifiedArgs[offs++], f.power()); })
    .template collect<Stack>();

  std::sort(args.begin(), args.end(), 
      [](auto& l, auto& r) { return l.term() < r.term(); });

  offs = 0;
  auto numeral = in.numeral;
  for (unsigned i = 0; i < args.size(); i++) {
    auto& arg = args[i];
    auto c = arg.term().template tryNumeral<Number>();
    if (c.isSome()) {
      // arg is a number constant
      numeral = numeral * pow(c.unwrap(), arg.power());
    } else {
      // arg is a non-number term
      auto term  = arg.term();
      auto power = arg.power();
      while (i + 1 < args.size() && args[i + 1].term() == term) {
        power += args[i + 1].power();
        i++;
      }
      if (power != 0)
        args[offs++] = MonomFactor(term, power);
    }
  }


  if (numeral == Numeral(0)) {
    return Monom::zero();
  } else {
    args.truncate(offs);
    return Monom(numeral, MonomFactors(std::move(args))); 
  }
}

TermList PolynomialEvaluation::evaluateToTerm(Term* in) const
{ return PolyNf::normalize(in).denormalize(); }

} // Inferences
