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
* @file LambdaConversion.hpp
* Defines class LambdaConversion.
*/

#ifndef __LambdaConversion__
#define __LambdaConversion__

//#if VHOL

#include "Lib/Deque.hpp"
#include "Forwards.hpp"

using namespace Kernel;
using namespace Shell;

/**
* A class that converts lambda terms from named to nameless (De Bruijn indices) representation.
*
* Along the way, it also converts formulas to terms with proxy symbols for connectives
*/
class LambdaConversion {
public:

    typedef std::pair<int,TermList> IndexSortPair;
    typedef DHMap<unsigned, IndexSortPair> VarToIndexMap;

    LambdaConversion() = delete;
 //  LambdaElimination(DHMap<unsigned,TermList> varSorts) : _varSorts(varSorts){};

    static TermList convertLambda(Term* lambdaTerm);
    static TermList convertLambda(TermList term);
    static TermList convertLambda(Formula*);

 //void addFunctionExtensionalityAxioms(UnitList*& units);
 //void addBooleanExtensionalityAxiom(UnitList*& units);

    static void addProxyAxioms(Problem& prb);
    static void addFunctionExtensionalityAxiom(Problem& prb);
    static void addChoiceAxiom(Problem& prb);
    static Literal* toEquality(TermList booleanTerm, bool polarity);

private:

    static TermList convertLambda(TermList term, VarToIndexMap& map);
    static TermList convertLambda(VList* vars, SList* sorts, TermList body, TermList bodySort, VarToIndexMap& map);
    static TermList convertLambda(Formula*, VarToIndexMap& map);

    static TermList sortOf(TermList t);
};

//#endif

#endif // __LambdaConversion__
