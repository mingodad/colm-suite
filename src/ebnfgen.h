/*
 * Copyright 2001-2018 Adrian Thurston <thurston@colm.net>
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

#ifndef _COLM_EBNFGEN_H
#define _COLM_EBNFGEN_H

#include <iostream>
#include <string>

struct LexJoin;
struct LexExpression;
struct LexTerm;
struct LexFactorAug;
struct LexFactorRep;
struct LexFactorNeg;
struct LexFactor;
struct Literal;
struct Range;
struct RegExpr;
struct ReItem;
enum BuiltinMachine;

/* Helper functions to convert lex expression trees to string patterns */
std::string lexJoinToPattern( LexJoin *lexJoin );
std::string lexExpressionToPattern( LexExpression *expr );
std::string lexTermToPattern( LexTerm *term );
std::string lexFactorAugToPattern( LexFactorAug *factorAug );
std::string lexFactorRepToPattern( LexFactorRep *factorRep );
std::string lexFactorNegToPattern( LexFactorNeg *factorNeg );
std::string lexFactorToPattern( LexFactor *factor );
std::string literalToPattern( Literal *literal );
std::string rangeToPattern( Range *range );
std::string regExprToPattern( RegExpr *regExp );
std::string reItemToPattern( ReItem *reItem );
std::string builtinMachineToPattern( BuiltinMachine builtin );

#endif /* _COLM_EBNFGEN_H */
