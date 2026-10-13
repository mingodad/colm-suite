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

#include <stdbool.h>
#include <iostream>
#include <sstream>
#include <map>
#include <set>
#include <string.h>

#include "compiler.h"

using namespace std;

static void writeLexJoin( ostream &, LexJoin * );
static void writeLexExpression( ostream &, LexExpression * );
static void writeLexTerm( ostream &, LexTerm * );
static void writeLexFactorAug( ostream &, LexFactorAug * );
static void writeLexFactorRep( ostream &, LexFactorRep * );
static void writeLexFactorNeg( ostream &, LexFactorNeg * );
static void writeLexFactor( ostream &, LexFactor * );

static void writeRegExpr( ostream &, RegExpr * );
static void writeReItem( ostream &, ReItem * );
static void writeReOrBlock( ostream &, ReOrBlock * );

/* Helper function to escape special characters in EBNF strings */
static void escapeEbnfString( ostream &out, const String &str )
{
	for ( const char *p = str.data; *p != 0; p++ ) {
		switch ( *p ) {
			case '\'': out << "\\'"; break;
			case '\\': out << "\\\\"; break;
			case '\n': out << "\\n"; break;
			case '\r': out << "\\r"; break;
			case '\t': out << "\\t"; break;
			default: out << *p; break;
		}
	}
}

/* Write out a language element name in EBNF format.
 * Handles repeat/list/opt elements by recursively outputting the
 * original element name with the appropriate EBNF suffix. */
static void writeEbnfName( ostream &out, LangEl *lel )
{
	/* Handle generated repeat/list/opt elements */
	if ( lel->repeatOf != 0 ) {
		/* Output the original element name with appropriate EBNF suffix */
		writeEbnfName( out, lel->repeatOf );
		if ( lel->isRepeat )
			out << "*";
		else if ( lel->isList )
			out << "+";
		else if ( lel->isOpt )
			out << "?";
		return;
	}
	
	if ( lel->isLiteral && lel->lit.length() > 0 ) {
		//out << "'";
		//escapeEbnfString( out, lel->lit );
		out << lel->lit;
		//out << "'";
	}
	else {
		out << lel->name;
	}
}

static void dumpLangEl( LangEl *lel )
{
    cerr
        << "LangEl"
        << " name=[" << lel->name << "]"
        << " type=" << lel->type
        << " repeat=" << lel->isRepeat
        << " list=" << lel->isList
        << " opt=" << lel->isOpt
        << " repeatOf=[";

    if ( lel->repeatOf != 0 )
        cerr << lel->repeatOf->name;

    cerr
        << "]"
        << " literal=" << lel->isLiteral
        << " prodCount=" << lel->prodList.length()
        << " tokenDef=" << (void *)lel->tokenDef
        << " termDup=" << (void *)lel->termDup
        << " rootDef=" << (void *)lel->rootDef
        << "\n";
}

/* Escape a literal for an EBNF single-quoted terminal. */
static void writeEbnfLiteral( ostream &out, const String &str )
{
	out << "'";

	for ( const char *p = str.data; *p != 0; p++ ) {
		switch ( *p ) {
			case '\'':
				out << "\\'";
				break;
			case '\\':
				out << "\\\\";
				break;
			case '\n':
				out << "\\n";
				break;
			case '\r':
				out << "\\r";
				break;
			case '\t':
				out << "\\t";
				break;
			default:
				out << *p;
				break;
		}
	}

	out << "'";
}

/* Output a Literal node. */
static void writeLiteral( ostream &out, Literal *literal )
{
	if ( literal == 0 )
		return;

	if ( literal->type == Literal::Number ) {
		out << literal->literal;
	}
	else {
		writeEbnfLiteral( out, literal->literal );
	}
}

static void writeLexLiteral( ostream &out, Literal *literal )
{
	if ( literal == 0 )
		return;

	out << literal->literal;
}

/* Output a character range. */
static void writeRange( ostream &out, Range *range )
{
	if ( range == 0 )
		return;

	out << "[";

	writeLiteral( out, range->lowerLit );
	out << "-";
	writeLiteral( out, range->upperLit );

	out << "]";
}

static void writeLexLiteralChar( ostream &out, Literal *literal )
{
	if ( literal == 0 )
		return;

	/*
	 * Literal::literal contains the Colm spelling, including the
	 * surrounding quotes. For a character range we want the character
	 * itself, not the quotes.
	 */
	const char *p = literal->literal.data;

	if ( *p == '\'' ) {
		p++;

		/* Skip the closing quote when writing the character. */
		if ( *p == '\\' ) {
			out << *p++;
			if ( *p != 0 )
				out << *p++;
		}
		else if ( *p != 0 ) {
			out << *p++;
		}
	}
	else {
		/* Numeric literal or unexpected representation. */
		out << literal->literal;
	}
}

static void writeLexRange( ostream &out, Range *range )
{
	if ( range == 0 )
		return;

	out << "[";

	writeLexLiteralChar( out, range->lowerLit );
	out << "-";
	writeLexLiteralChar( out, range->upperLit );

	out << "]";
}

/* Convert a Colm builtin lexical machine to a useful textual name. */
static const char *builtinName( BuiltinMachine builtin )
{
	switch ( builtin ) {
		case BT_Any:    return "ANY";
		case BT_Ascii:  return "ASCII";
		case BT_Extend: return "EXTEND";
		case BT_Alpha:  return "ALPHA";
		case BT_Digit:  return "DIGIT";
		case BT_Alnum:  return "ALNUM";
		case BT_Lower:  return "LOWER";
		case BT_Upper:  return "UPPER";
		case BT_Cntrl:  return "CNTRL";
		case BT_Graph:  return "GRAPH";
		case BT_Print:  return "PRINT";
		case BT_Punct:  return "PUNCT";
		case BT_Space:  return "SPACE";
		case BT_Xdigit: return "XDIGIT";
		case BT_Lambda: return "LAMBDA";
		case BT_Empty:  return "EMPTY";
	}

	return "UNKNOWN";
}

static void writeReData( ostream &out, const String &data )
{
	for ( const char *p = data.data; *p != 0; p++ ) {
		switch ( *p ) {
			case '\\':
				out << "\\\\";
				break;
			case '\n':
				out << "\\n";
				break;
			case '\r':
				out << "\\r";
				break;
			case '\t':
				out << "\\t";
				break;
			default:
				out << *p;
				break;
		}
	}
}

static void writeReChar( ostream &out, char c )
{
	switch ( c ) {
		case '\\':
			out << "\\\\";
			break;
		case ']':
			out << "\\]";
			break;
		case '[':
			out << "\\[";
			break;
		case '-':
			out << "\\-";
			break;
		case '^':
			out << "\\^";
			break;
		case '\n':
			out << "\\n";
			break;
		case '\r':
			out << "\\r";
			break;
		case '\t':
			out << "\\t";
			break;
		default:
			out << c;
			break;
	}
}

static void writeReItem( ostream &out, ReItem *item )
{
	if ( item == 0 )
		return;

	switch ( item->type ) {
		case ReItem::Data:
			/*
			 * ReItem::data is already the character data from the
			 * regular-expression parser. Escape it so that it remains
			 * readable in the generated EBNF.
			 */
			writeReData( out, item->data );
			break;

		case ReItem::Dot:
			out << ".";
			break;

		case ReItem::OrBlock:
			out << "[";
			if ( item->orBlock != 0 ) {
				/* ReOrBlock is handled by writeReOrBlock(). */
				writeReOrBlock( out, item->orBlock );
			}
			out << "]";
			break;

		case ReItem::NegOrBlock:
			out << "[^";
			if ( item->orBlock != 0 )
				writeReOrBlock( out, item->orBlock );
			out << "]";
			break;
	}
}

static void writeReOrItem( ostream &out, ReOrItem *item );

static void writeReOrBlock( ostream &out, ReOrBlock *block )
{
	if ( block == 0 )
		return;

	if ( block->type == ReOrBlock::RecurseItem ) {
		writeReOrBlock( out, block->orBlock );
		writeReOrItem( out, block->item );
	}
}

static void writeReOrItem( ostream &out, ReOrItem *item )
{
	if ( item == 0 )
		return;

	switch ( item->type ) {
		case ReOrItem::Data:
			escapeEbnfString( out, item->data );
			break;

		case ReOrItem::Range:
			/*
			 * This is the internal regex representation of:
			 *
			 *     lower-upper
			 *
			 * Keep it recognizable in the generated output.
			 */
			writeReChar( out, item->lower );
			out << "-";
			writeReChar( out, item->upper );
			break;
	}
}

static void writeRegExpr( ostream &out, RegExpr *expr )
{
	if ( expr == 0 )
		return;

	if ( expr->type == RegExpr::RecurseItem ) {
		writeRegExpr( out, expr->regExp );
		writeReItem( out, expr->item );
	}
}

static void writeLexFactor( ostream &out, LexFactor *factor )
{
	switch ( factor->type ) {
		case LexFactor::LiteralType:
			writeLexLiteral( out, factor->literal );
			break;

		case LexFactor::RangeType:
			writeLexRange( out, factor->range );
			break;

		case LexFactor::OrExprType:
			writeReItem( out, factor->reItem );
			break;

		case LexFactor::RegExprType:
			writeRegExpr( out, factor->regExp );
			break;

		case LexFactor::ReferenceType:
			if ( factor->varDef != 0 )
				out << factor->varDef->name;
			else
				out << "<null-reference>";
			break;

		case LexFactor::ParenType:
			out << "(";
			writeLexJoin( out, factor->join );
			out << ")";
			break;
	}
}

static void writeLexFactorNeg( ostream &out, LexFactorNeg *neg )
{
	switch ( neg->type ) {
		case LexFactorNeg::NegateType:
			out << "^";
			writeLexFactorNeg( out, neg->factorNeg );
			break;

		case LexFactorNeg::CharNegateType:
			out << "^";
			writeLexFactorNeg( out, neg->factorNeg );
			break;

		case LexFactorNeg::FactorType:
			writeLexFactor( out, neg->factor );
			break;
	}
}

static void writeLexFactorRep( ostream &out, LexFactorRep *rep )
{
	switch ( rep->type ) {
		case LexFactorRep::StarType:
			writeLexFactorRep( out, rep->factorRep );
			out << "*";
			break;

		case LexFactorRep::StarStarType:
			writeLexFactorRep( out, rep->factorRep );
			out << "**";
			break;

		case LexFactorRep::OptionalType:
			writeLexFactorRep( out, rep->factorRep );
			out << "?";
			break;

		case LexFactorRep::PlusType:
			writeLexFactorRep( out, rep->factorRep );
			out << "+";
			break;

		case LexFactorRep::ExactType:
			writeLexFactorRep( out, rep->factorRep );
			out << "{" << rep->lowerRep << "}";
			break;

		case LexFactorRep::MaxType:
			writeLexFactorRep( out, rep->factorRep );
			out << "{," << rep->upperRep << "}";
			break;

		case LexFactorRep::MinType:
			writeLexFactorRep( out, rep->factorRep );
			out << "{" << rep->lowerRep << ",}";
			break;

		case LexFactorRep::RangeType:
			writeLexFactorRep( out, rep->factorRep );
			out << "{"
			    << rep->lowerRep
			    << ","
			    << rep->upperRep
			    << "}";
			break;

		case LexFactorRep::FactorNegType:
			writeLexFactorNeg( out, rep->factorNeg );
			break;
	}
}

static void writeLexFactorAug( ostream &out, LexFactorAug *aug )
{
	writeLexFactorRep( out, aug->factorRep );
}

static void writeLexTerm( ostream &out, LexTerm *term )
{
	switch ( term->type ) {
		case LexTerm::ConcatType:
			writeLexTerm( out, term->term );
			out << " ";
			writeLexFactorAug( out, term->factorAug );
			break;

		case LexTerm::RightStartType:
			out << "(";
			writeLexTerm( out, term->term );
			out << " :> ";
			writeLexFactorAug( out, term->factorAug );
			out << ")";
			break;

		case LexTerm::RightFinishType:
			out << "(";
			writeLexTerm( out, term->term );
			out << " :>> ";
			writeLexFactorAug( out, term->factorAug );
			out << ")";
			break;

		case LexTerm::LeftType:
			out << "(";
			writeLexTerm( out, term->term );
			out << " <: ";
			writeLexFactorAug( out, term->factorAug );
			out << ")";
			break;

		case LexTerm::FactorAugType:
			writeLexFactorAug( out, term->factorAug );
			break;
	}
}

static void writeLexExpression( ostream &out, LexExpression *expr )
{
	switch ( expr->type ) {
		case LexExpression::OrType:
			out << "(";
			writeLexExpression( out, expr->expression );
			out << " | ";
			writeLexTerm( out, expr->term );
			out << ")";
			break;

		case LexExpression::IntersectType:
			out << "(";
			writeLexExpression( out, expr->expression );
			out << " & ";
			writeLexTerm( out, expr->term );
			out << ")";
			break;

		case LexExpression::SubtractType:
			out << "(";
			writeLexExpression( out, expr->expression );
			out << " - ";
			writeLexTerm( out, expr->term );
			out << ")";
			break;

		case LexExpression::StrongSubtractType:
			out << "(";
			writeLexExpression( out, expr->expression );
			out << " -- ";
			writeLexTerm( out, expr->term );
			out << ")";
			break;

		case LexExpression::TermType:
			writeLexTerm( out, expr->term );
			break;

		case LexExpression::BuiltinType:
			out << builtinName( expr->builtin );
			break;
	}
}

static void writeLexJoin( ostream &out, LexJoin *join )
{
	if ( join == 0 || join->expr == 0 ) {
		out << "<empty>";
		return;
	}

	writeLexExpression( out, join->expr );
}

/* Write out token definitions from lex blocks */
void Compiler::writeEbnfTokens()
{
    ostream &out = *outStream;
    bool hasTokens = false;

    for ( NamespaceList::Iter ns = namespaceList; ns.lte(); ns++ ) {
        if ( ns->tokenDefList.length() > 0 ) {
            hasTokens = true;
            break;
        }
    }

    if ( !hasTokens )
        return;

    out << "/* Lexical regions:\n";

    for ( RegionSetList::Iter rs = regionSetList; rs.lte(); rs++ ) {
		//if (strcmp(rs->loc.fileName, "-") == 0) continue;
        out << " * [region set " << rs->id << "]";

        if ( rs->loc.fileName != 0 )
            out << " at " << rs->loc.fileName;

        out << ":" << rs->loc.line << "\n";
    }

    out << " */\n\n";

    out << "/* Tokens (Colm lexical expressions):\n";

    for ( NamespaceList::Iter ns = namespaceList; ns.lte(); ns++ ) {
        for ( TokenDefListNs::Iter tok = ns->tokenDefList;
                tok.lte(); tok++ ) {

            out << " * " << tok->name
                << " [region set " << tok->regionSet->id << "]";

            if ( tok->isIgnore )
                out << " (ignored)";

            out << " ::= ";

            if ( tok->isLiteral ) {
                writeEbnfLiteral( out, tok->literal );
            }
            else if ( tok->join != 0 ) {
                writeLexJoin( out, tok->join );
            }
            else {
                out << "<no expression>";
            }

            out << "\n";
        }
    }

    out << " */\n\n";
}

/* Write out a production in EBNF format */
void Compiler::writeEbnfProduction( Production *prod )
{
	ostream &out = *outStream;
	
	/* Output production elements */
	for ( ProdEl *el = prod->prodElList->head; el != 0; el = el->next ) {
		if ( el != prod->prodElList->head )
			out << " ";
		writeEbnfName( out, el->langEl );
	}
}

/* Write out all productions for a non-terminal */
void Compiler::writeEbnfLangEl( LangEl *lel )
{
    ostream &out = *outStream;

    /* Skip compiler-generated repetition/list/optional elements. */
    if ( lel->isRepeat || lel->isList || lel->isOpt )
        return;

    /* Skip terminals. */
    if ( lel->type != LangEl::NonTerm )
        return;

    /* Skip the compiler's synthetic root. */
	if ( lel == rootLangEl )
    	return;

    /* Skip elements with no productions. */
    if ( lel->prodList.length() == 0 )
        return;

    out << lel->name << "\n";

    bool first = true;
    for ( LelProdList::Iter prod = lel->prodList;
          prod.lte(); prod++ ) {
        if ( first ) {
            out << "    ::= ";
            first = false;
        }
        else {
            out << "\n      | ";
        }

        writeEbnfProduction( prod );
    }

    out << "\n\n";
}

/* Main EBNF generation function */
void Compiler::writeEbnfFile()
{
	ostream &out = *outStream;
	
	//for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) dumpLangEl( lel );

	out << "/* EBNF grammar generated by Colm */\n";
	out << "/* Compatible with https://www.bottlecaps.de/rr/ui */\n\n";
	
	/* Output tokens */
	writeEbnfTokens();
	
	/* Output productions */
	out << "/* Productions */\n\n";
	
	/* Iterate through all language elements */
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ )
		writeEbnfLangEl( lel );
}

/*
 * SQL dump of the grammar. Writes SQL text to outStream that can be loaded
 * into SQLite (sqlite3 grammars.db < dump.sql). Every table is keyed by a
 * grammar id so several grammars can be stored in one database and compared
 * or searched with SQL. --dump-sql[=N] selects the grammar id (default 1).
 */

static void sqlWriteStr( ostream &out, const char *s )
{
	if ( s == 0 || *s == 0 ) {
		out << "NULL";
		return;
	}

	out << '\'';
	for ( const char *p = s; *p != 0; p++ ) {
		if ( *p == '\'' )
			out << "''";
		else
			out << *p;
	}
	out << '\'';
}

/* The lexical pattern of a token as written in the source. */
static void sqlWritePattern( ostream &out, LangEl *lel )
{
	TokenDef *tok = lel->tokenDef;
	if ( tok == 0 ) {
		out << "NULL";
		return;
	}

	ostringstream buf;

	if ( tok->isLiteral ) {
		buf << '\'';
		escapeEbnfString( buf, tok->literal );
		buf << '\'';
	}
	else if ( tok->join != 0 ) {
		writeLexJoin( buf, tok->join );
	}

	if ( buf.str().empty() )
		out << "NULL";
	else
		sqlWriteStr( out, buf.str().c_str() );
}

void Compiler::writeSqlFile()
{
	ostream &out = *outStream;

	/* Tokens declared through a namespace (lex region tokens, literals,
	 * ignores). Internal filler tokens made for empty scanner regions don't
	 * go through a namespace and are excluded from the pattern column. */
	std::set<LangEl*> userTokens;
	for ( NamespaceList::Iter ns = namespaceList; ns.lte(); ns++ ) {
		for ( TokenDefListNs::Iter tok = ns->tokenDefList; tok.lte(); tok++ ) {
			if ( tok->tdLangEl != 0 )
				userTokens.insert( tok->tdLangEl );
		}
	}

	out << "BEGIN;\n\n";

	out << "CREATE TABLE IF NOT EXISTS grammar(\n"
			"  id INTEGER PRIMARY KEY,\n"
			"  name TEXT NOT NULL,\n"
			"  dumped TEXT DEFAULT (datetime('now'))\n"
			");\n";
	out << "INSERT INTO grammar(id,name) VALUES(" << dumpSqlGrammarId << ",";
	sqlWriteStr( out, inputFn != 0 ? inputFn : "grammar" );
	out << ");\n\n";

	out << "CREATE TABLE IF NOT EXISTS langel(\n"
			"  grammar_id INTEGER NOT NULL REFERENCES grammar(id),\n"
			"  id INTEGER NOT NULL,\n"
			"  name TEXT,\n"
			"  lit TEXT,\n"
			"  kind TEXT NOT NULL CHECK(kind IN"
				" ('terminal','nonterminal','synthetic')),\n"
			"  is_literal BOOLEAN NOT NULL,\n"
			"  is_repeat BOOLEAN NOT NULL,\n"
			"  is_list BOOLEAN NOT NULL,\n"
			"  is_opt BOOLEAN NOT NULL,\n"
			"  repeat_of INTEGER,\n"
			"  pattern TEXT,\n"
			"  pred_type CHAR CHECK(pred_type IN ('L','R','N','P')),\n"
			"  pred_value INTEGER,\n"
			"  is_root BOOLEAN NOT NULL,\n"
			"  PRIMARY KEY(grammar_id,id)\n"
			");\n";

	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		const char *kind;
		if ( lel->isRepeat || lel->isList || lel->isOpt )
			kind = "synthetic";
		else if ( lel->type == LangEl::NonTerm )
			kind = "nonterminal";
		else
			kind = "terminal";

		out << "INSERT INTO langel VALUES(" << dumpSqlGrammarId
			<< "," << lel->id << ",";
		sqlWriteStr( out, lel->name );
		out << ",";
		sqlWriteStr( out, lel->lit );
		out << ",'" << kind << "',"
			<< ( lel->isLiteral ? 1 : 0 ) << ","
			<< ( lel->isRepeat ? 1 : 0 ) << ","
			<< ( lel->isList ? 1 : 0 ) << ","
			<< ( lel->isOpt ? 1 : 0 ) << ",";

		if ( lel->repeatOf != 0 )
			out << lel->repeatOf->id;
		else
			out << "NULL";

		out << ",";
		if ( userTokens.count( lel ) != 0 )
			sqlWritePattern( out, lel );
		else
			out << "NULL";
		out << ",";

		switch ( lel->predType ) {
		case PredLeft:
			out << "'L'";
			break;
		case PredRight:
			out << "'R'";
			break;
		case PredNonassoc:
			out << "'N'";
			break;
		case PredPrecedence:
			out << "'P'";
			break;
		default:
			out << "NULL";
			break;
		}

		out << ",";
		if ( lel->predType == PredNone )
			out << "NULL";
		else
			out << lel->predValue;

		out << "," << ( lel == rootLangEl ? 1 : 0 ) << ");\n";
	}

	out << "\n";

	/* Collect the distinct files productions come from, so productions
	 * reference a file id instead of repeating the file name. */
	std::map<std::string,long> fileIds;
	long nextFileId = 1;

	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		for ( LelProdList::Iter prod = lel->prodList;
				prod.lte(); prod++ )
		{
			if ( prod->loc.fileName != 0 && *prod->loc.fileName != 0 &&
					strcmp( prod->loc.fileName, "-" ) != 0 )
			{
				long &id = fileIds[ prod->loc.fileName ];
				if ( id == 0 )
					id = nextFileId++;
			}
		}
	}

	out << "CREATE TABLE IF NOT EXISTS file(\n"
			"  grammar_id INTEGER NOT NULL REFERENCES grammar(id),\n"
			"  id INTEGER NOT NULL,\n"
			"  name TEXT NOT NULL,\n"
			"  PRIMARY KEY(grammar_id,id)\n"
			");\n";

	for ( std::map<std::string,long>::iterator it = fileIds.begin();
			it != fileIds.end(); it++ )
	{
		out << "INSERT INTO file VALUES(" << dumpSqlGrammarId
			<< "," << it->second << ",";
		sqlWriteStr( out, it->first.c_str() );
		out << ");\n";
	}

	out << "\n";

	out << "CREATE TABLE IF NOT EXISTS production(\n"
			"  grammar_id INTEGER NOT NULL,\n"
			"  prod_id INTEGER NOT NULL,\n"
			"  prod_num INTEGER NOT NULL,\n"
			"  lhs_id INTEGER NOT NULL,\n"
			"  loc_file_id INTEGER,\n"
			"  loc_line INTEGER,\n"
			"  PRIMARY KEY(grammar_id,prod_id),\n"
			"  FOREIGN KEY(grammar_id,lhs_id)"
				" REFERENCES langel(grammar_id,id),\n"
			"  FOREIGN KEY(grammar_id,loc_file_id)"
				" REFERENCES file(grammar_id,id)\n"
			");\n";

	out << "CREATE TABLE IF NOT EXISTS prod_el(\n"
			"  grammar_id INTEGER NOT NULL,\n"
			"  prod_id INTEGER NOT NULL,\n"
			"  pos INTEGER NOT NULL,\n"
			"  el_id INTEGER NOT NULL,\n"
			"  PRIMARY KEY(grammar_id,prod_id,pos),\n"
			"  FOREIGN KEY(grammar_id,prod_id)"
				" REFERENCES production(grammar_id,prod_id),\n"
			"  FOREIGN KEY(grammar_id,el_id)"
				" REFERENCES langel(grammar_id,id)\n"
			");\n\n";

	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		for ( LelProdList::Iter prod = lel->prodList;
				prod.lte(); prod++ )
		{
			out << "INSERT INTO production VALUES(" << dumpSqlGrammarId
				<< "," << prod->prodId
				<< "," << prod->prodNum
				<< "," << lel->id << ",";

			long fileId = 0;
			if ( prod->loc.fileName != 0 && *prod->loc.fileName != 0 &&
					strcmp( prod->loc.fileName, "-" ) != 0 )
				fileId = fileIds[ prod->loc.fileName ];

			if ( fileId != 0 )
				out << fileId << "," << prod->loc.line;
			else
				out << "NULL,NULL";
			out << ");\n";

			int pos = 0;
			for ( ProdEl *el = prod->prodElList->head;
					el != 0; el = el->next )
			{
				if ( el->langEl == 0 )
					continue;

				out << "INSERT INTO prod_el VALUES("
					<< dumpSqlGrammarId
					<< "," << prod->prodId
					<< "," << pos++
					<< "," << el->langEl->id << ");\n";
			}
		}
	}

	out << "\n";

	/* Views that render the grammar back as text, in the spirit of the
	 * grammar_view of the byacc sql dump. Elements generated for
	 * repeat/list/opt wrappers are folded back into name* / name+ / name?. */
	out <<
		"CREATE VIEW IF NOT EXISTS prod_el_view AS\n"
		"SELECT pe.grammar_id AS grammar_id,\n"
		"       pe.prod_id AS prod_id,\n"
		"       pe.pos AS pos,\n"
		"       CASE WHEN b.kind = 'synthetic'\n"
		"            THEN CASE WHEN o.is_literal=1"
						" AND coalesce(o.lit,'')<>''\n"
		"                      THEN o.lit ELSE o.name END\n"
		"                 || CASE WHEN b.is_opt THEN '?'"
						" WHEN b.is_list THEN '+' ELSE '*' END\n"
		"            ELSE CASE WHEN b.is_literal=1"
						" AND coalesce(b.lit,'')<>''\n"
		"                      THEN b.lit ELSE b.name END\n"
		"       END AS el_text\n"
		"FROM prod_el AS pe\n"
		"JOIN langel AS b ON b.grammar_id=pe.grammar_id AND b.id=pe.el_id\n"
		"LEFT JOIN langel AS o ON o.grammar_id=pe.grammar_id"
				" AND o.id=b.repeat_of;\n\n"

		"CREATE VIEW IF NOT EXISTS rule_view AS\n"
		"SELECT r.grammar_id AS grammar_id,\n"
		"       r.prod_id AS prod_id,\n"
		"       r.prod_num AS prod_num,\n"
		"       l.name AS lhs,\n"
		"       l.kind AS lhs_kind,\n"
		"       l.is_root AS is_root,\n"
		"       r.loc_file_id AS loc_file_id,\n"
		"       coalesce((\n"
		"         SELECT group_concat(el_text, ' ')\n"
		"         FROM ( SELECT el_text, pos FROM prod_el_view\n"
		"                WHERE grammar_id=r.grammar_id"
						" AND prod_id=r.prod_id\n"
		"                ORDER BY pos ) ), '/*empty*/') AS rhs\n"
		"FROM production AS r\n"
		"JOIN langel AS l ON l.grammar_id=r.grammar_id"
				" AND l.id=r.lhs_id;\n\n"

		"CREATE VIEW IF NOT EXISTS def_view AS\n"
		"SELECT grammar_id, lhs,\n"
		"  'def ' || lhs || ' [' || group_concat(rhs, ' | ') || '];'"
				" AS def_text\n"
		"FROM ( SELECT grammar_id, lhs, prod_num, rhs, is_root, lhs_kind\n"
		"       FROM rule_view ORDER BY grammar_id, lhs, prod_num )\n"
		"WHERE NOT is_root AND lhs_kind<>'synthetic'\n"
		"GROUP BY grammar_id, lhs;\n\n"

		"CREATE VIEW IF NOT EXISTS token_view AS\n"
		"SELECT grammar_id,\n"
		"  CASE WHEN is_literal=1\n"
		"       THEN 'literal ' || coalesce(lit, name) || ';'\n"
		"       ELSE 'lex token ' || name || coalesce(' ' || pattern, '') || ';' END\n"
		"       AS decl\n"
		"FROM langel\n"
		"WHERE pattern IS NOT NULL;\n\n"

		"CREATE VIEW IF NOT EXISTS prec_view AS\n"
		"SELECT grammar_id,\n"
		"  CASE pred_type WHEN 'L' THEN 'left' WHEN 'R' THEN 'right'\n"
		"   WHEN 'N' THEN 'nonassoc' ELSE 'precedence' END\n"
		"  || ' ' || coalesce(name, lit) AS decl\n"
		"FROM langel\n"
		"WHERE pred_type IS NOT NULL;\n\n"

		"CREATE VIEW IF NOT EXISTS start_view AS\n"
		"/* Best effort: the start symbol is the user nonterminal that is never\n"
		" * referenced in the right hand side of a user production. The true start\n"
		" * comes from the parse statement in the program body. */\n"
		"SELECT DISTINCT r.grammar_id, r.lhs AS start_symbol\n"
		"FROM rule_view AS r\n"
		"WHERE NOT r.is_root AND r.loc_file_id IS NOT NULL\n"
		"  AND r.lhs NOT IN ( SELECT pe.el_text FROM prod_el_view AS pe\n"
		"                     JOIN production AS p\n"
		"                       ON p.grammar_id=pe.grammar_id"
							" AND p.prod_id=pe.prod_id\n"
		"                     WHERE pe.grammar_id=r.grammar_id"
							" AND p.loc_file_id IS NOT NULL );\n\n"

		"CREATE VIEW IF NOT EXISTS grammar_view AS\n"
		"SELECT grammar_id, decl AS line FROM token_view\n"
		"UNION ALL\n"
		"SELECT grammar_id, decl FROM prec_view\n"
		"UNION ALL\n"
		"SELECT grammar_id, def_text FROM def_view;\n\n"

		"COMMIT;\n"
		"-- The grammar as text: SELECT line FROM grammar_view"
				" WHERE grammar_id=1;\n"
		"-- Load another grammar with --dump-sql=2 into the same db, then\n"
		"-- compare: SELECT * FROM grammar_view WHERE grammar_id=2\n"
		"--   EXCEPT SELECT * FROM grammar_view WHERE grammar_id=1;\n";
}
