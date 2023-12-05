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
 * @file LiteralIndex.hpp
 * Defines class LiteralIndex.
 */


#ifndef __LiteralIndex__
#define __LiteralIndex__

#include "Lib/DHMap.hpp"

#include "Index.hpp"
#include "LiteralIndexingStructure.hpp"


namespace Indexing {

template<class Data>
class LiteralIndex
: public Index
{
public:
  USE_ALLOCATOR(LiteralIndex);

  VirtualIterator<LiteralClause> getAll()
  { return _is->getAll(); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LiteralClause>> getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions = true)
  { return _is->getUnifications(lit, complementary, retrieveSubstitutions); }

  VirtualIterator<QueryRes<AbstractingUnifier*, Data>> getUwa(Literal* lit, bool complementary, Options::UnificationWithAbstraction uwa, bool fixedPointIteration)
  { return _is->getUwa(lit, complementary, uwa, fixedPointIteration); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LiteralClause>> getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions = true)
  { return _is->getGeneralizations(lit, complementary, retrieveSubstitutions); }

  VirtualIterator<QueryRes<ResultSubstitutionSP, LiteralClause>> getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions = true)
  { return _is->getInstances(lit, complementary, retrieveSubstitutions); }

  size_t getUnificationCount(Literal* lit, bool complementary)
  { return _is->getUnificationCount(lit, complementary); }


protected:
  LiteralIndex(LiteralIndexingStructure<Data>* is) : _is(is) {}

  void handleLiteral(Literal* lit, Clause* cl, bool add)
  { _is->handle(Data(cl, lit), add); }

  std::unique_ptr<LiteralIndexingStructure<Data>> _is;
};

class BinaryResolutionIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(BinaryResolutionIndex);

  BinaryResolutionIndex(LiteralIndexingStructure<LiteralClause>* is)
  : LiteralIndex<LiteralClause>(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class BackwardSubsumptionIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(BackwardSubsumptionIndex);

  BackwardSubsumptionIndex(LiteralIndexingStructure<LiteralClause>* is)
  : LiteralIndex<LiteralClause>(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class FwSubsSimplifyingLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(FwSubsSimplifyingLiteralIndex);

  FwSubsSimplifyingLiteralIndex(LiteralIndexingStructure<LiteralClause>* is)
    : LiteralIndex<LiteralClause>(is)
  { }

protected:
  void handleClause(Clause* c, bool adding) override;
};

class FSDLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(FSDLiteralIndex);

  FSDLiteralIndex(LiteralIndexingStructure<LiteralClause>* is)
    : LiteralIndex<LiteralClause>(is)
  { }

protected:
  void handleClause(Clause* c, bool adding) override;
};

class UnitClauseLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(UnitClauseLiteralIndex);

  UnitClauseLiteralIndex(LiteralIndexingStructure<LiteralClause>* is)
  : LiteralIndex<LiteralClause>(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class UnitClauseWithALLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(UnitClauseWithALLiteralIndex);

  UnitClauseWithALLiteralIndex(LiteralIndexingStructure<LiteralClause>* is)
  : LiteralIndex(is) {};
protected:
  void handleClause(Clause* c, bool adding);
};

class NonUnitClauseLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(NonUnitClauseLiteralIndex);

  NonUnitClauseLiteralIndex(LiteralIndexingStructure<LiteralClause>* is, bool selectedOnly=false)
  : LiteralIndex<LiteralClause>(is), _selectedOnly(selectedOnly) {};
protected:
  void handleClause(Clause* c, bool adding);
private:
  bool _selectedOnly;
};

class NonUnitClauseWithALLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(NonUnitClauseWithALLiteralIndex);

  NonUnitClauseWithALLiteralIndex(LiteralIndexingStructure<LiteralClause>* is, bool selectedOnly=false)
  : LiteralIndex(is), _selectedOnly(selectedOnly) {};
protected:
  void handleClause(Clause* c, bool adding);
private:
  bool _selectedOnly;
};

class RewriteRuleIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(RewriteRuleIndex);

  RewriteRuleIndex(LiteralIndexingStructure<LiteralClause>* is, Ordering& ordering);
  ~RewriteRuleIndex();

  Clause* getCounterpart(Clause* c) {
    return _counterparts.get(c);
  }
protected:
  void handleClause(Clause* c, bool adding);
  Literal* getGreater(Clause* c);

private:
  void handleEquivalence(Clause* c, Literal* cgr, Clause* d, Literal* dgr, bool adding);

  LiteralIndexingStructure<LiteralClause>* _partialIndex;
  DHMap<Clause*,Clause*> _counterparts;
  Ordering& _ordering;
};

class DismatchingLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(DismatchingLiteralIndex);

  DismatchingLiteralIndex(LiteralIndexingStructure<LiteralClause>* is)
  : LiteralIndex<LiteralClause>(is) {};
  void handleClause(Clause* c, bool adding);
  void addLiteral(Literal* c);
};

class UnitIntegerComparisonLiteralIndex
: public LiteralIndex<LiteralClause>
{
public:
  USE_ALLOCATOR(UnitIntegerComparisonLiteralIndex);

  UnitIntegerComparisonLiteralIndex(LiteralIndexingStructure<LiteralClause>* is)
  : LiteralIndex<LiteralClause>(is) {}

protected:
  void handleClause(Clause* c, bool adding);
};

};

#endif /* __LiteralIndex__ */
