

#ifndef __POLYNOMIAL_NORMALIZATION_H__
#define __POLYNOMIAL_NORMALIZATION_H__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/Theory.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class Cancellation
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(Cancellation);
  USE_ALLOCATOR(Cancellation);

  virtual ~Cancellation();

  Clause* simplify(Clause* cl);
};


class PushUnaryMinus
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(PushUnaryMinus);
  USE_ALLOCATOR(PushUnaryMinus);

  virtual ~PushUnaryMinus();

  Clause* simplify(Clause* cl);
};


class PolynomialNormalization
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(PolynomialNormalization);
  USE_ALLOCATOR(PolynomialNormalization);

  /* will not check whether it performed an actual simplification */
  PolynomialNormalization();

  /* 
   * will use the simplification ordering in order to check whether 
   * its transformation were an actual simplification 
   */
  PolynomialNormalization(Ordering& ordering);
  virtual ~PolynomialNormalization();

  Clause* simplify(Clause* cl);
private:

  PolynomialNormalizer<PolynomialNormalizerConfig::Simplification<>> _normalizer;
  Ordering* _ordering;
};

};

#endif /* __POLYNOMIAL_NORMALIZATION_H__ */
