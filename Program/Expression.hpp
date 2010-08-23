/**
 * @file Expression.hpp
 * Defines class Program::Expression
 *
 * @since 20/08/2010, Torrevieja
 */

#ifndef __ProgramExpression__
#define __ProgramExpression__

#include <string>
#include "Debug/Assertion.hpp"
#include "Lib/Stack.hpp"

using namespace std;
using namespace Lib;

namespace Program {

class Type;
class Variable;

/**
 * Expressions used in programs
 * @since 20/08/2010, Torrevieja
 */
class Expression
{
public:
	enum Kind {
		/** constant integer */
		CONSTANT_INTEGER,
		/** constant (built-in) function */
		CONSTANT_FUNCTION,
		/** variable */
		VARIABLE,
		/** function application */
		FUNCTION_APPLICATION,
		/** array expression applied to an argument */
		ARRAY_APPLICATION
	};
	/** the kind */
	Kind kind() const {return _kind; }

	/** checks whether the expresssion is an lvalue */
	virtual bool lvalue() const = 0;
	/** convert to expression to a string, can be used to output the expression */
	virtual string toString() const = 0;

	/** return the type of the expression */
	const Type* etype() const
	{
		ASS(_type);
		return _type;
	}

	/** the main constructor */
	explicit Expression(Kind k) : _kind(k) {}

	/**
	 * Class for itering over subexpressions of an expression. It is
	 * guaranteed that an expression is always returned before any of
	 * its proper subexpressions.
	 */
	class SubexpressionIterator {
	public:
		/** create a subexpression iterator for an expression @b expr */
		explicit SubexpressionIterator(Expression* expr)
		{
			_stack.push(expr);
		}
		/** true if there is at least one subexpression left */
		bool hasNext() const
		{
			return ! _stack.isEmpty();
		}
		Expression* next();
	protected:
		Stack<Expression*> _stack;
	};
protected:
	/** the kind */
	const Kind _kind;
	/** the type */
	const Type* _type;
}; // class Expression

/**
 * Constant integer expressions
 * @since 20/08/2010, Torrevieja
 */
class ConstantIntegerExpression
	: public Expression
{
public:
	explicit ConstantIntegerExpression(int val);
	bool lvalue() const;
	string toString() const;
protected:
	/** the value of this expression */
	int _value;
}; // class ConstantIntegerExpression

/**
 * Constant (built-in) functions
 * @since 21/08/2010, Torrevieja
 */
class ConstantFunctionExpression
	: public Expression
{
public:
	bool lvalue() const;
	string toString() const;

	static ConstantFunctionExpression* integerEq();
	static ConstantFunctionExpression* integerLess(); 
	static ConstantFunctionExpression* integerLessEq(); 
	static ConstantFunctionExpression* integerGreater(); 
	static ConstantFunctionExpression* integerGreaterEq(); 
	static ConstantFunctionExpression* integerPlus(); 
	static ConstantFunctionExpression* integerMinus(); 
	static ConstantFunctionExpression* integerNegation();
	static ConstantFunctionExpression* integerMult(); 
protected:
	/** the name of this expression */
	string _name;
private:
	ConstantFunctionExpression(const char* name,Type* tp);
	/** true if initialized */
	static bool _initialized;
	/** initialize all built-ins */
	static void initialize();

	/** integer equality */
	static ConstantFunctionExpression* _integerEq;
	/** integer less than */
	static ConstantFunctionExpression* _integerLess;
	/** integer less than or equal to */
	static ConstantFunctionExpression* _integerLessEq; 
	/** integer greater than */
	static ConstantFunctionExpression* _integerGreater;
	/** integer greater than or equal to */
	static ConstantFunctionExpression* _integerGreaterEq;
	/** integer plus */
	static ConstantFunctionExpression* _integerPlus;
	/** integer minus */
	static ConstantFunctionExpression* _integerMinus;
	/** integer unary minus */
	static ConstantFunctionExpression* _integerNegation;
	/** integer product */
	static ConstantFunctionExpression* _integerMult;
}; // class ConstantFunctionExpression

/**
 * Variable expression
 * @since 20/08/2010, Torrevieja
 */
class VariableExpression
	: public Expression
{
public:
	explicit VariableExpression(Variable* v);
	bool lvalue() const;
	string toString() const;
	/** the variable */
	Variable* variable() const {return _variable;}
protected:
	/** the variable of this expression */
	Variable* _variable;
}; // class ConstantIntegerExpression

/**
 * Function application expressions
 * @since 20/08/2010, Torrevieja
 */
class FunctionApplicationExpression
	: public Expression
{
public:
	explicit FunctionApplicationExpression(Expression* fun);
	bool lvalue() const;
	string toString() const;
	void setArgument(unsigned argNumber,Expression* e);
	/** return the function */
	Expression* function() const { return _function; }
	/** return the argument number @b n */
	Expression* getArgument(unsigned n)
	{
		ASS(n < _numberOfArguments);
		ASS(_arguments[n]);
		return _arguments[n];
	}
	/** number of arguments */
	unsigned numberOfArguments() const {return _numberOfArguments;}
protected:
	/** the value of this expression */
	Expression* _function;
	/** number of arguments */
	unsigned _numberOfArguments;
	/** array of arguments */
	Expression** _arguments;
}; // class FunctionApplicationExpression

/**
 * Array application expressions
 * @since 21/08/2010, Torrevieja
 */
class ArrayApplicationExpression
	: public Expression
{
public:
	ArrayApplicationExpression(Expression* arr,Expression* arg);
	bool lvalue() const;
	string toString() const;
	/** return the array expression */
	Expression* array() const { return _array; }
	/** return the argument expression */
	Expression* argument() const { return _argument; }
protected:
	/** the array expression */
	Expression* _array;
	/** the argument expression */
	Expression* _argument;
}; // class ArrayApplicationExpression

}

#endif // __ProgramExpression__
