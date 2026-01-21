/*
 * Copyright 2006-2018 Adrian Thurston <thurston@colm.net>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#include <iostream>
#include <sstream>
#include <iomanip>

#include "compiler.h"
#include "ebnfgen.h"
#include "parsetree.h"

using namespace std;

/* Helper to escape special characters in string literals */
static string escapeString( const string &str )
{
	ostringstream escaped;
	for ( size_t i = 0; i < str.length(); i++ ) {
		unsigned char c = str[i];
		switch ( c ) {
			case '\n': escaped << "\\n"; break;
			case '\t': escaped << "\\t"; break;
			case '\r': escaped << "\\r"; break;
			case '\\': escaped << "\\\\"; break;
			case '\'': escaped << "\\'"; break;
			default:
				if ( c >= 32 && c <= 126 )
					escaped << c;
				else {
					/* Print as hex escape */
					escaped << "\\x" << std::hex << std::setfill('0') << std::setw(2) << (int)c << std::dec;
				}
				break;
		}
	}
	return escaped.str();
}

/* Convert a Literal to a pattern string */
string literalToPattern( Literal *literal )
{
	if ( literal == 0 )
		return "";
	
	if ( literal->type == Literal::LitString ) {
		return "'" + escapeString( literal->literal.data ) + "'";
	}
	else {
		/* Number literal */
		return literal->literal.data;
	}
}

/* Convert a Range to a pattern string */
string rangeToPattern( Range *range )
{
	if ( range == 0 )
		return "";
	
	string lower = literalToPattern( range->lowerLit );
	string upper = literalToPattern( range->upperLit );
	return lower + " .. " + upper;
}

/* Convert builtin machine to pattern string */
string builtinMachineToPattern( BuiltinMachine builtin )
{
	switch ( builtin ) {
		case BT_Any: return "any";
		case BT_Ascii: return "ascii";
		case BT_Extend: return "extend";
		case BT_Alpha: return "alpha";
		case BT_Digit: return "digit";
		case BT_Alnum: return "alnum";
		case BT_Lower: return "lower";
		case BT_Upper: return "upper";
		case BT_Cntrl: return "cntrl";
		case BT_Graph: return "graph";
		case BT_Print: return "print";
		case BT_Punct: return "punct";
		case BT_Space: return "space";
		case BT_Xdigit: return "xdigit";
		case BT_Lambda: return "";
		case BT_Empty: return "''";
		default: return "unknown_builtin";
	}
}

/* Forward declarations for recursive structures */
string reOrBlockToPattern( ReOrBlock *orBlock );
string reOrItemToPattern( ReOrItem *orItem );

/* Convert ReOrItem to pattern string */
string reOrItemToPattern( ReOrItem *orItem )
{
	if ( orItem == 0 )
		return "";
	
	if ( orItem->type == ReOrItem::Data ) {
		return escapeString( orItem->data.data );
	}
	else if ( orItem->type == ReOrItem::Range ) {
		ostringstream result;
		result << (char)orItem->lower << "-" << (char)orItem->upper;
		return result.str();
	}
	
	return "";
}

/* Convert ReOrBlock to pattern string */
string reOrBlockToPattern( ReOrBlock *orBlock )
{
	if ( orBlock == 0 )
		return "";
	
	if ( orBlock->type == ReOrBlock::Empty )
		return "";
	
	string result;
	if ( orBlock->orBlock != 0 )
		result = reOrBlockToPattern( orBlock->orBlock );
	
	if ( orBlock->item != 0 ) {
		string itemStr = reOrItemToPattern( orBlock->item );
		if ( !result.empty() && !itemStr.empty() )
			result += itemStr;
		else
			result += itemStr;
	}
	
	return result;
}

/* Convert ReItem to pattern string */
string reItemToPattern( ReItem *reItem )
{
	if ( reItem == 0 )
		return "";
	
	switch ( reItem->type ) {
		case ReItem::Data:
			return escapeString( reItem->data.data );
		case ReItem::Dot:
			return ".";
		case ReItem::OrBlock:
			return "[" + reOrBlockToPattern( reItem->orBlock ) + "]";
		case ReItem::NegOrBlock:
			return "[^" + reOrBlockToPattern( reItem->orBlock ) + "]";
		default:
			return "";
	}
}

/* Convert RegExpr to pattern string */
string regExprToPattern( RegExpr *regExp )
{
	if ( regExp == 0 )
		return "";
	
	if ( regExp->type == RegExpr::Empty )
		return "";
	
	string result;
	if ( regExp->regExp != 0 )
		result = regExprToPattern( regExp->regExp );
	
	if ( regExp->item != 0 )
		result += reItemToPattern( regExp->item );
	
	return result;
}

/* Convert LexFactor to pattern string */
string lexFactorToPattern( LexFactor *factor )
{
	if ( factor == 0 )
		return "";
	
	switch ( factor->type ) {
		case LexFactor::LiteralType:
			return literalToPattern( factor->literal );
		
		case LexFactor::RangeType:
			return "[" + rangeToPattern( factor->range ) + "]";
		
		case LexFactor::OrExprType:
			/* OrExpr is a ReItem, handled like regex character class */
			return reItemToPattern( factor->reItem );
		
		case LexFactor::RegExprType:
			return regExprToPattern( factor->regExp );
		
		case LexFactor::ReferenceType:
			/* Reference to another token - use its name */
			if ( factor->varDef != 0 && factor->varDef->name.data != 0 && factor->varDef->name.length() > 0 )
				return factor->varDef->name.data;
			return "";
		
		case LexFactor::ParenType:
			/* Parenthesized expression */
			if ( factor->join != 0 )
				return "( " + lexJoinToPattern( factor->join ) + " )";
			return "";
		
		default:
			return "";
	}
}

/* Convert LexFactorNeg to pattern string */
string lexFactorNegToPattern( LexFactorNeg *factorNeg )
{
	if ( factorNeg == 0 )
		return "";
	
	switch ( factorNeg->type ) {
		case LexFactorNeg::NegateType:
			return "!" + lexFactorNegToPattern( factorNeg->factorNeg );
		
		case LexFactorNeg::CharNegateType:
			return "^" + lexFactorNegToPattern( factorNeg->factorNeg );
		
		case LexFactorNeg::FactorType:
			return lexFactorToPattern( factorNeg->factor );
		
		default:
			return "";
	}
}

/* Convert LexFactorRep to pattern string */
string lexFactorRepToPattern( LexFactorRep *factorRep )
{
	if ( factorRep == 0 )
		return "";
	
	string base;
	
	switch ( factorRep->type ) {
		case LexFactorRep::StarType:
			base = lexFactorRepToPattern( factorRep->factorRep );
			return base + "*";
		
		case LexFactorRep::StarStarType:
			base = lexFactorRepToPattern( factorRep->factorRep );
			return base + "**";
		
		case LexFactorRep::OptionalType:
			base = lexFactorRepToPattern( factorRep->factorRep );
			return base + "?";
		
		case LexFactorRep::PlusType:
			base = lexFactorRepToPattern( factorRep->factorRep );
			return base + "+";
		
		case LexFactorRep::ExactType:
			base = lexFactorRepToPattern( factorRep->factorRep );
			{
				ostringstream result;
				result << base << "{" << factorRep->lowerRep << "}";
				return result.str();
			}
		
		case LexFactorRep::MaxType:
			base = lexFactorRepToPattern( factorRep->factorRep );
			{
				ostringstream result;
				result << base << "{," << factorRep->upperRep << "}";
				return result.str();
			}
		
		case LexFactorRep::MinType:
			base = lexFactorRepToPattern( factorRep->factorRep );
			{
				ostringstream result;
				result << base << "{" << factorRep->lowerRep << ",}";
				return result.str();
			}
		
		case LexFactorRep::RangeType:
			base = lexFactorRepToPattern( factorRep->factorRep );
			{
				ostringstream result;
				result << base << "{" << factorRep->lowerRep << "," << factorRep->upperRep << "}";
				return result.str();
			}
		
		case LexFactorRep::FactorNegType:
			return lexFactorNegToPattern( factorRep->factorNeg );
		
		default:
			return "";
	}
}

/* Convert LexFactorAug to pattern string */
string lexFactorAugToPattern( LexFactorAug *factorAug )
{
	if ( factorAug == 0 )
		return "";
	
	return lexFactorRepToPattern( factorAug->factorRep );
}

/* Convert LexTerm to pattern string */
string lexTermToPattern( LexTerm *term )
{
	if ( term == 0 )
		return "";
	
	string result;
	
	switch ( term->type ) {
		case LexTerm::ConcatType:
			/* Concatenation of term and factorAug */
			result = lexTermToPattern( term->term );
			if ( !result.empty() )
				result += " ";
			result += lexFactorAugToPattern( term->factorAug );
			return result;
		
		case LexTerm::RightStartType:
		case LexTerm::RightFinishType:
		case LexTerm::LeftType:
			/* These are precedence operators - for pattern output, just concat */
			result = lexTermToPattern( term->term );
			if ( !result.empty() )
				result += " ";
			result += lexFactorAugToPattern( term->factorAug );
			return result;
		
		case LexTerm::FactorAugType:
			return lexFactorAugToPattern( term->factorAug );
		
		default:
			return "";
	}
}

/* Convert LexExpression to pattern string */
string lexExpressionToPattern( LexExpression *expr )
{
	if ( expr == 0 )
		return "";
	
	string result;
	
	switch ( expr->type ) {
		case LexExpression::OrType:
			result = lexExpressionToPattern( expr->expression );
			if ( !result.empty() )
				result += " | ";
			result += lexTermToPattern( expr->term );
			return result;
		
		case LexExpression::IntersectType:
			result = lexExpressionToPattern( expr->expression );
			if ( !result.empty() )
				result += " & ";
			result += lexTermToPattern( expr->term );
			return result;
		
		case LexExpression::SubtractType:
			result = lexExpressionToPattern( expr->expression );
			if ( !result.empty() )
				result += " - ";
			result += lexTermToPattern( expr->term );
			return result;
		
		case LexExpression::StrongSubtractType:
			result = lexExpressionToPattern( expr->expression );
			if ( !result.empty() )
				result += " -- ";
			result += lexTermToPattern( expr->term );
			return result;
		
		case LexExpression::TermType:
			return lexTermToPattern( expr->term );
		
		case LexExpression::BuiltinType:
			return builtinMachineToPattern( expr->builtin );
		
		default:
			return "";
	}
}

/* Convert LexJoin to pattern string */
string lexJoinToPattern( LexJoin *lexJoin )
{
	if ( lexJoin == 0 )
		return "";
	
	return lexExpressionToPattern( lexJoin->expr );
}

/* Write EBNF output for all tokens */
void Compiler::writeEbnfTokens()
{
	ostream &out = *outStream;
	
	out << "/* EBNF Token Definitions */\n\n";
	
	/* Iterate through all namespaces and their tokens */
	for ( NamespaceList::Iter ns = namespaceList; ns.lte(); ns++ ) {
		for ( TokenDefListNs::Iter tok = ns->tokenDefList; tok.lte(); tok++ ) {
			out << tok->name.data << "\n";
			out << "    ::= ";
			
			if ( tok->isLiteral && tok->literal.data != 0 && tok->literal.length() > 0 ) {
				/* Literal token - output the literal value */
				out << "'" << escapeString( tok->literal.data ) << "'";
			}
			else if ( tok->join != 0 ) {
				/* Regex token - convert the LexJoin tree to a pattern */
				string pattern = lexJoinToPattern( tok->join );
				if ( !pattern.empty() )
					out << pattern;
				else
					out << "/* empty pattern */";
			}
			else {
				/* No pattern available */
				out << "/* no pattern */";
			}
			
			out << "\n\n";
		}
	}
}
