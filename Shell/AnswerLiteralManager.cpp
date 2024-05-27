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
 * @file AnswerExtractor.cpp
 * Implements class AnswerExtractor.
 */

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/MainLoop.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndexingStructure.hpp"

#include "Shell/Flattening.hpp"
#include "Shell/Options.hpp"

#include "Parse/TPTP.hpp"

#include "AnswerLiteralManager.hpp"

static bool isProperAnswerClause(Clause* cl) {
  return !cl->isEmpty() && forAll(cl->iterLits(),[] (Literal* l) { return l->isAnswerLiteral(); } );
}

namespace Inferences
{

Clause* AnswerLiteralResolver::simplify(Clause* cl)
{
  if (isProperAnswerClause(cl)) {
    return AnswerLiteralManager::getInstance()->getRefutation(cl);
  }
  return cl;
}

}


namespace Shell
{

using namespace std;
typedef List<pair<unsigned,pair<Clause*, Literal*>>> AnsList;

///////////////////////
// AnswerLiteralManager
//

AnswerLiteralManager* AnswerLiteralManager::getInstance()
{
  static AnswerLiteralManager* instance =
    (env.options->questionAnswering() == Options::QuestionAnsweringMode::PLAIN) ?
      static_cast<AnswerLiteralManager*>(new PlainALManager()) :
      static_cast<AnswerLiteralManager*>(new SynthesisALManager());

  return instance;
}

void AnswerLiteralManager::addAnswerLiterals(Problem& prb)
{
  if(addAnswerLiterals(prb.units())) {
    prb.invalidateProperty();
  }
}

/**
 * Attempt adding answer literals into questions among the units
 * in the list @c units. Return true if some answer literal was added.
 */
bool AnswerLiteralManager::addAnswerLiterals(UnitList*& units)
{
  bool someAdded = false;
  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    Unit* newU = tryAddingAnswerLiteral(u);
    if(u!=newU) {
      someAdded = true;
      uit.replace(newU);
    }
  }
  return someAdded;
}

Unit* AnswerLiteralManager::tryAddingAnswerLiteral(Unit* unit)
{
  if (unit->isClause() || (unit->inputType()!=UnitInputType::CONJECTURE && unit->inputType()!=UnitInputType::NEGATED_CONJECTURE)) {
    return unit; // do nothing
  }

  Formula* topF = static_cast<FormulaUnit*>(unit)->formula();

  // it must start with a not
  if(topF->connective()!=NOT) {
    return unit; // do nothing
  }

  Formula* subNot = topF->uarg();

  bool skolemise = false;
  Formula* eQuant;
  if (subNot->connective() == EXISTS) {
    eQuant = subNot;
  } else if (subNot->connective() == FORALL) {
    skolemise = true;
    Formula* subForall = subNot->qarg();
    if (subForall->connective() == EXISTS) {
      eQuant = subForall;
    } else {
      return unit; // do nothing
    }
  } else {
    return unit; // do nothing
  }

  VList* eVars = eQuant->vars();
  SList* eSrts = eQuant->sorts();
  ASS(eVars);

  FormulaList* conjArgs = 0;
  FormulaList::push(eQuant->qarg(), conjArgs);
  Literal* ansLit = getAnswerLiteral(eVars,eSrts,eQuant);
  _originUnitsAndInjectedLiterals.insert(ansLit->functor(),make_pair(unit,ansLit));
  FormulaList::push(new AtomicFormula(ansLit), conjArgs);

  Formula* out = new NegatedFormula(new QuantifiedFormula(EXISTS, eVars, eSrts, new JunctionFormula(AND, conjArgs)));

  if (skolemise) {
    VList* fVars = subNot->vars();
    SList* fSrts = subNot->sorts();
    Substitution subst;
    while (VList::isNonEmpty(fVars)) {
      unsigned var = fVars->head();
      fVars = fVars->tail();
      unsigned skFun = env.signature->addSkolemFunction(/*arity=*/0, /*suffix=*/"in", /*computable=*/true);
      Signature::Symbol* skSym = env.signature->getFunction(skFun);
      TermList sort;
      if (SList::isNonEmpty(fSrts)) {
        sort = fSrts->head();
        fSrts = fSrts->tail();
      } else {
        sort = AtomicSort::defaultSort();
      }
      OperatorType* ot = OperatorType::getConstantsType(sort);
      skSym->setType(ot);
      Term* skTerm = Term::create(skFun, /*arity=*/0, /*args=*/nullptr);
      subst.bind(var, skTerm);
      recordSkolemBinding(skTerm, var);
    }
    out = SubstHelper::apply(out, subst);
  }

  return new FormulaUnit(out, FormulaTransformation(skolemise ? InferenceRule::ANSWER_LITERAL_INPUT_SKOLEMISATION : InferenceRule::ANSWER_LITERAL_INJECTION, unit));
}

TermList AnswerLiteralManager::possiblyEvaluateAnswerTerm(TermList aT)
{
  if(aT.isTerm() && !aT.term()->isSpecial()){
    InterpretedLiteralEvaluator eval;
    unsigned p = env.signature->addFreshPredicate(1,"p");
    TermList sort = SortHelper::getResultSort(aT.term());
    OperatorType* type = OperatorType::getPredicateType({sort});
    env.signature->getPredicate(p)->setType(type);
    Literal* l = Literal::create1(p,true,aT);
    Literal* res =0;
    bool constant, constTrue;
    Stack<Literal*> sideConditions;
    bool litMod = eval.evaluate(l,constant,res,constTrue,sideConditions);
    if(litMod && res && sideConditions.isEmpty()){
      aT.setTerm(res->nthArgument(0)->term());
    }
  }
  return aT;
}

void AnswerLiteralManager::tryOutputAnswer(Clause* refutation)
{
  Stack<Clause*> answer;

  if (!tryGetAnswer(refutation, answer)) {
    return;
  }
  std::cout << "% SZS answers Tuple [";
  if (answer.size() > 1) {
    std::cout << "(";
  }
  Stack<Clause*>::BottomFirstIterator aIt(answer);
  while(aIt.hasNext()) {
    Clause* aCl = aIt.next();
    auto varIt = aCl->getVariableIterator();
    if (varIt.hasNext()) {
      cout << "∀";
      while(varIt.hasNext()) {
        cout << TermList(varIt.next(),false).toString();
        if (varIt.hasNext()) {
          cout << ",";
        }
      }
      cout << ".";
    }
    if (aCl->size() > 1) {
      cout << "(";
    }
    auto lIt = aCl->iterLits();
    while (lIt.hasNext()) {
      Literal* aLit = lIt.next();
      std::cout << "[";
      unsigned arity = aLit->arity();

      Map<int,vstring>* questionVars = 0;
      std::pair<Unit*,Literal*> unitAndLiteral;
      if (_originUnitsAndInjectedLiterals.find(aLit->functor(),unitAndLiteral)) {
        questionVars = Parse::TPTP::findQuestionVars(unitAndLiteral.first->number());
      }

      for(unsigned i=0; i<arity; i++) {
        if(i > 0) {
          std::cout << ',';
        }
        if (questionVars) {
          cout << questionVars->get(unitAndLiteral.second->nthArgument(i)->var()) << "->";
        }
        std::cout << possiblyEvaluateAnswerTerm(*aLit->nthArgument(i));
      }
      std::cout << "]";
      if(lIt.hasNext()) {
        std::cout << "|";
      }
    }
    if (aCl->size() > 1) {
      cout << ")";
    }
    if(aIt.hasNext()) {
      std::cout << "|";
    }
  }
  if (answer.size() > 1) {
    std::cout << ")";
  }
  std::cout << "|_] for " << env.options->problemName() << endl;
}

static bool pushFirstPremiseToAnswerIfFromResolver(Inference& inf, Stack<Clause*>& answer)
{
  if (inf.rule() == InferenceRule::UNIT_RESULTING_RESOLUTION) {
    auto it = inf.iterator();
    ASS(inf.hasNext(it));
    Clause* firstParent = inf.next(it)->asClause();
    // cout << firstParent->toNiceString() << endl;
    if (isProperAnswerClause(firstParent)) {
      answer.push(firstParent);
      return true;
    }
  }
  return false;
}

bool AnswerLiteralManager::tryGetAnswer(Clause* refutation, Stack<Clause*>& answer)
{
  ASS(refutation->isEmpty());

  Inference& inf = refutation->inference();
  if (pushFirstPremiseToAnswerIfFromResolver(inf,answer)) {
    return true;
  } else if (inf.rule() == InferenceRule::AVATAR_REFUTATION) {
    bool added = false;
    auto it = inf.iterator();
    while (inf.hasNext(it)) {
      Unit* prem = inf.next(it);
      Inference& inf2 = prem->inference();
      if (inf2.rule() == InferenceRule::AVATAR_CONTRADICTION_CLAUSE) {
        auto it2 = inf2.iterator();
        Unit* anEmpty = inf2.next(it2);
        ASS(!inf2.hasNext(it2));
        Inference& inf3 = anEmpty->inference();
        added |= pushFirstPremiseToAnswerIfFromResolver(inf3,answer);
      }
    }
    return added;
  }
  // currently does nothing for AVATAR_REFUTATION_SMT (which does not get minimized)

  return false;
}

Literal* AnswerLiteralManager::getAnswerLiteral(VList* vars,SList* srts,Formula* f)
{
  static Stack<TermList> litArgs;
  litArgs.reset();
  TermStack sorts;
  while(VList::isNonEmpty(vars)) {
    unsigned var = vars->head();
    vars = vars->tail();
    TermList sort;
    if (SList::isNonEmpty(srts)) {
      sort = srts->head();
      srts = srts->tail();
    } else {
      sort = AtomicSort::defaultSort();
    }
    litArgs.push(TermList(var, false));
    sorts.push(sort);
  }

  unsigned vcnt = litArgs.size();
  unsigned pred = env.signature->addFreshPredicate(vcnt,"ans");
  Signature::Symbol* predSym = env.signature->getPredicate(pred);
  predSym->setType(OperatorType::getPredicateType(sorts.size(), sorts.begin()));
  predSym->markAnswerPredicate();
  // don't need equality proxy for answer literals
  predSym->markSkipCongruence();
  return Literal::create(pred, vcnt, true, false, litArgs.begin());
}

Clause* AnswerLiteralManager::getResolverClause(unsigned pred)
{
  Clause* res;
  if(_resolverClauses.find(pred, res)) {
    return res;
  }

  static Stack<TermList> args;
  args.reset();

  Signature::Symbol* predSym = env.signature->getPredicate(pred);
  ASS(predSym->answerPredicate());
  unsigned arity = predSym->arity();

  for(unsigned i=0; i<arity; i++) {
    args.push(TermList(i, false));
  }
  Literal* lit = Literal::create(pred, arity, true, false, args.begin());
  res = Clause::fromIterator(getSingletonIterator(lit),NonspecificInference0(UnitInputType::AXIOM,InferenceRule::ANSWER_LITERAL_RESOLVER));

  _resolverClauses.insert(pred, res);
  return res;
}

Clause* AnswerLiteralManager::getRefutation(Clause* answer)
{
  unsigned clen = answer->length();
  UnitList* premises = 0;

  for(unsigned i=0; i<clen; i++) {
    Clause* resolvingPrem = getResolverClause((*answer)[i]->functor());
    UnitList::push(resolvingPrem, premises);
  }

  // finally, put in the actual answer clause (for an easier retrieval later)
  UnitList::push(answer, premises);

  Clause* refutation = Clause::fromIterator(LiteralIterator::getEmpty(),
      GeneratingInferenceMany(InferenceRule::UNIT_RESULTING_RESOLUTION, premises));
  return refutation;
}

///////////////////////
// PlainALManager
//

void PlainALManager::recordSkolemBinding(Term*,unsigned)
{

}

///////////////////////
// SynthesisALManager
//

void SynthesisALManager::getNeededUnits(Clause* refutation, ClauseStack& premiseClauses, Stack<Unit*>& conjectures, DHSet<Unit*>& allProofUnits)
{
  Stack<Unit*> toDo;
  toDo.push(refutation);

  while(toDo.isNonEmpty()) {
    Unit* curr = toDo.pop();
    if(!allProofUnits.insert(curr)) {
      continue;
    }
    Inference& inf = curr->inference();
    InferenceRule infRule = inf.rule();
    if(infRule==InferenceRule::NEGATED_CONJECTURE) {
      conjectures.push(curr);
    }
    if(infRule==InferenceRule::CLAUSIFY ||
	    (curr->isClause() && (infRule==InferenceRule::INPUT || infRule==InferenceRule::NEGATED_CONJECTURE )) ){
      ASS(curr->isClause());
      premiseClauses.push(curr->asClause());
    }
    auto it = inf.iterator();
    while(inf.hasNext(it)) {
      Unit* premise = inf.next(it);
      toDo.push(premise);
    }
  }
}

void SynthesisALManager::recordSkolemBinding(Term* skTerm, unsigned var)
{
  _skolemReplacement.bindSkolemToVar(skTerm, var);
}

bool SynthesisALManager::tryGetAnswer(Clause* refutation, Stack<Clause*>& answer)
{
  if (!_lastAnsLit && AnsList::isEmpty(_answerPairs)) {
    return false;
  }
  if (_lastAnsLit) {
    AnsList::push(make_pair(0, make_pair(nullptr, _lastAnsLit)), _answerPairs);
  }

  Stack<TermList> answerArgs;

  ClauseStack premiseClauses;
  Stack<Unit*> conjectures;
  DHSet<Unit*> proofUnits;
  getNeededUnits(refutation, premiseClauses, conjectures, proofUnits);
  DHSet<unsigned> proofNums;
  DHSet<Unit*>::Iterator puit(proofUnits);
  while (puit.hasNext()) proofNums.insert(puit.next()->number());

  AnsList::Iterator it(_answerPairs);
  ALWAYS(it.hasNext());
  pair<unsigned, pair<Clause*, Literal*>> p = it.next();
  Literal* origLit = p.second.second;
  unsigned arity = origLit->arity();
  Stack<TermList> sorts(arity);
  for (unsigned i = 0; i < arity; i++) {
    sorts.push(env.signature->getPredicate(origLit->functor())->predType()->arg(i));
    answerArgs.push(_skolemReplacement.transformTermList(*origLit->nthArgument(i), sorts[i]));
  }
  while(it.hasNext()) {
    p = it.next();
    ASS(p.second.first != nullptr);
    ASS(p.first == p.second.first->number());
    if (!proofNums.contains(p.first)) {
      continue;
    }
    // Create the condition for an if-then-else by negating the clause
    Formula* condition = getConditionFromClause(p.second.first);
    for (unsigned i = 0; i < arity; i++) {
      ASS_EQ(sorts[i], env.signature->getPredicate(p.second.second->functor())->predType()->arg(i));
      // Construct the answer using if-then-else
      answerArgs[i] = TermList(Term::createITE(condition, _skolemReplacement.transformTermList(*p.second.second->nthArgument(i), sorts[i]), answerArgs[i], sorts[i]));
    }
  }
  // just a single literal answer
  Clause* answerCl = new (1) Clause(1, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::INPUT));
  (*answerCl)[0] = Literal::create(origLit,answerArgs.begin());
  answer.push(answerCl);
  return true;
}

void SynthesisALManager::onNewClause(Clause* cl)
{
  if(!cl->noSplits() || cl->isEmpty() || (cl->length() != 1) || !(*cl)[0]->isAnswerLiteral()) {
    return;
  }

  ASS(cl->hasAnswerLiteral())

  Literal* lit = cl->getAnswerLiteral();
  if (!lit->computableOrVar())
    return;
  _lastAnsLit = lit;

  Clause* refutation = getRefutation(cl);
  throw MainLoop::RefutationFoundException(refutation);
}

Clause* SynthesisALManager::recordAnswerAndReduce(Clause* cl) {
  if (!cl->noSplits() || !cl->hasAnswerLiteral() || !cl->computable()) {
    return nullptr;
  }
  // Check if the answer literal has only distinct variables as arguments.
  // If yes, we do not need to record the clause, because the answer literal
  // represents any answer.
  unsigned clen = cl->length();
  bool removeDefaultAnsLit = true;
  Literal* ansLit = cl->getAnswerLiteral();
  Set<unsigned> vars;
  for (unsigned i = 0; i < ansLit->numTermArguments(); ++i) {
    TermList* tl = ansLit->nthArgument(i);
    if (!tl->isVar()) {
      removeDefaultAnsLit = false;
      break;
    }
    vars.insert(tl->var());
  }
  if (vars.size() != ansLit->numTermArguments()) {
    removeDefaultAnsLit = false;
  }

  unsigned nonAnsLits = 0;
  for(unsigned i=0; i<clen; i++) {
    if((*cl)[i] != ansLit) {
      nonAnsLits++;
    }
  }
  ASS_EQ(nonAnsLits, clen-1);

  Inference inf(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_REMOVAL, cl));
  Clause* newCl = new(nonAnsLits) Clause(nonAnsLits, inf);
  unsigned idx = 0;
  for (unsigned i = 0; i < clen; i++) {
    if ((*cl)[i] != ansLit) {
      (*newCl)[idx++] = (*cl)[i];
    }
  }
  if (!removeDefaultAnsLit) {
    AnsList::push(make_pair(newCl->number(), make_pair(newCl, ansLit)), _answerPairs);
  } else {
    _lastAnsLit = ansLit;
  }
  return newCl;
}

Literal* SynthesisALManager::makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit) {
  ASS(Literal::headersMatch(thenLit, elseLit, /*complementary=*/false));

  Signature::Symbol* predSym = env.signature->getPredicate(thenLit->functor());
  Stack<TermList> litArgs;
  Term* condTerm = translateToSynthesisConditionTerm(condition);
  for (unsigned i = 0; i < thenLit->arity(); ++i) {
    TermList* ttl = thenLit->nthArgument(i);
    TermList* etl = elseLit->nthArgument(i);
    if (ttl == etl) {
      litArgs.push(*ttl);
    } else {
      litArgs.push(TermList(createRegularITE(condTerm, *ttl, *etl, predSym->predType()->arg(i))));
    }
  }
  return Literal::create(thenLit->functor(), thenLit->arity(), thenLit->polarity(), /*commutative=*/false, litArgs.begin());
}

Formula* SynthesisALManager::getConditionFromClause(Clause* cl) {
  FormulaList* fl = FormulaList::empty();
  for (unsigned i = 0; i < cl->length(); ++i) {
    Literal* newLit = Literal::complementaryLiteral(_skolemReplacement.transformLiteral((*cl)[i]));
    FormulaList::push(new AtomicFormula(newLit), fl);
  }
  return JunctionFormula::generalJunction(Connective::AND, fl);
}

/** Create a new complex term, with its top-level function symbol
 *  created as a dummy symbol representing the predicate of @b l, and copy
 *  from the array @b args its arguments. Insert it into the sharing
 *  structure if all arguments are shared.
 */
Term* SynthesisALManager::translateToSynthesisConditionTerm(Literal* l)
{
  ASS_EQ(l->getPreDataSize(), 0);
  ASS(!l->isSpecial());

  unsigned arity = l->arity();
  vstring fnName = "cond_";
  if (l->isNegative()) {
    fnName.append("not_");
  }
  fnName.append(l->predicateName());
  if (l->isEquality()) {
    fnName.append(SortHelper::getEqualityArgumentSort(l).toString());
  }
  bool added = false;
  unsigned fn = env.signature->addFunction(fnName, arity, added);
  // Store the mapping between the function and predicate symbols
  _skolemReplacement.addCondPair(fn, l->functor());
  if (added) {
    Signature::Symbol* sym = env.signature->getFunction(fn);
    Stack<TermList> argSorts;
    if (l->isEquality()) {
      TermList as = SortHelper::getEqualityArgumentSort(l);
      argSorts.push(as);
      argSorts.push(as);
    } else {
      OperatorType* ot = env.signature->getPredicate(l->functor())->predType();
      for (unsigned i = 0; i < arity; ++i) {
        argSorts.push(ot->arg(i));
      }
      if (!env.signature->getPredicate(l->functor())->computable()) {
        sym->markUncomputable();
      }
    }
    sym->setType(OperatorType::getFunctionType(arity, argSorts.begin(), AtomicSort::defaultSort()));
  }
  
  Stack<TermList> args;
  for (unsigned i = 0; i < arity; ++i) {
    args.push(*(l->nthArgument(i)));
  }
  return Term::create(fn, arity, args.begin());
}

/**
 * Create a (condition ? thenBranch : elseBranch) expression
 * and return the resulting term
 */
Term* SynthesisALManager::createRegularITE(Term* condition, TermList thenBranch, TermList elseBranch, TermList branchSort)
{
  unsigned itefn = getITEFunctionSymbol(branchSort);
  return Term::create(itefn, {TermList(condition), thenBranch, elseBranch});
}

void SynthesisALManager::ConjectureSkolemReplacement::bindSkolemToVar(Term* t, unsigned v) {
  ASS(_skolemToVar.count(t) == 0);
  _skolemToVar[t] = v;
}

TermList SynthesisALManager::ConjectureSkolemReplacement::transformTermList(TermList tl, TermList sort) {
  // First replace free variables by 0-like constants
  if (tl.isVar() || (tl.isTerm() && !tl.term()->ground())) {
    TermList zero(theory->representConstant(IntegerConstantType(0)));
    if (tl.isVar()) {
      if (sort == AtomicSort::intSort()) {
        return zero;
      } else {
        vstring name = "cz_" + sort.toString();
        unsigned czfn;
        if (!env.signature->tryGetFunctionNumber(name, 0, czfn)) {
          czfn = env.signature->addFreshFunction(0, name.c_str());
          env.signature->getFunction(czfn)->setType(OperatorType::getConstantsType(sort));
        } 
        TermList res(Term::createConstant(czfn));
        return res;
      }
    } else {
      Substitution s;
      vset<unsigned> done;
      Kernel::VariableWithSortIterator vit(tl.term());
      while (vit.hasNext()) {
        pair<TermList, TermList> p = vit.next();
        unsigned v = p.first.var();
        TermList& vsort = p.second;
        if (done.count(v) == 0) {
          done.insert(v);
          if (vsort == AtomicSort::intSort()) {
            s.bind(v, zero);
          } else {
            vstring name = "cz_" + vsort.toString();
            unsigned czfn;
            if (!env.signature->tryGetFunctionNumber(name, 0, czfn)) {
              czfn = env.signature->addFreshFunction(0, name.c_str());
              env.signature->getFunction(czfn)->setType(OperatorType::getConstantsType(sort));
            }
            TermList res(Term::createConstant(czfn));
            s.bind(v, res);
          }
        }
      }
      tl = TermList(tl.term()->apply(s));
    }
  }
  // Then replace skolems by variables
  return transform(tl);
}

TermList SynthesisALManager::ConjectureSkolemReplacement::transformSubterm(TermList trm) {
  if (trm.isTerm()) {
    auto it = _skolemToVar.find(trm.term());
    if (it != _skolemToVar.end()) {
      return TermList(it->second, false);
    }
    Term* t = trm.term();
    if ((t->arity() == 3) && t->nthArgument(0)->isTerm()) {
      TermList sort = env.signature->getFunction(t->functor())->fnType()->arg(1);
      if (t->functor() == getITEFunctionSymbol(sort)) {
        // Build condition
        Term* tcond = t->nthArgument(0)->term();
        vstring condName = tcond->functionName();
        unsigned pred = _condFnToPred.get(tcond->functor());
        Stack<TermList> args;
        for (unsigned i = 0; i < tcond->arity(); ++i) args.push(transform(*(tcond->nthArgument(i))));
        Literal* newCond;
        if (env.signature->isEqualityPredicate(pred)) {
          newCond = Literal::createEquality(/*polarity=*/true, args[0], args[1], sort);
        } else {
          newCond = Literal::create(pred, tcond->arity(), /*polarity=*/true, /*commutative=*/false, args.begin());
        }
        // Build the whole ITE term
        return TermList(Term::createITE(new AtomicFormula(newCond), transform(*(t->nthArgument(1))), transform(*(t->nthArgument(2))), sort));
      }
    }
  }
  return trm;
}

}
