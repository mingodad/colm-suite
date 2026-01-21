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

#include "compiler.h"

using namespace std;

/* Helper function to escape strings for EBNF output */
static void writeEbnfString( ostream &out, const String &str )
{
	out << "'";
	for ( int i = 0; i < str.length(); i++ ) {
		char c = str[i];
		switch ( c ) {
			case '\'': out << "\\'"; break;
			case '\\': out << "\\\\"; break;
			case '\n': out << "\\n"; break;
			case '\t': out << "\\t"; break;
			case '\r': out << "\\r"; break;
			default:
				if ( c >= 32 && c <= 126 )
					out << c;
				else {
					out << "\\x";
					char hex[3];
					snprintf( hex, sizeof(hex), "%02x", (unsigned char)c );
					out << hex;
				}
				break;
		}
	}
	out << "'";
}

/* Helper function to write language element name */
static void writeLangElName( ostream &out, LangEl *lel )
{
	if ( lel->isLiteral ) {
		/* For literal tokens, output the literal string */
		writeEbnfString( out, lel->lit );
	}
	else {
		/* For non-terminals and named tokens, output the name */
		out << lel->name;
	}
}

void Compiler::writeEbnf()
{
	ostream &out = *outStream;
	
	/* Iterate through all language elements */
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		/* Only process non-terminals that have productions */
		if ( lel->type == LangEl::NonTerm && lel->prodList.length() > 0 ) {
			/* Skip internal/generated non-terminals (those starting with _) */
			if ( lel->name.length() > 0 && lel->name[0] == '_' )
				continue;
			
			/* Output the non-terminal name */
			out << lel->name << "\n";
			out << "    ::= ";
			
			bool firstProd = true;
			/* Iterate through all productions for this non-terminal */
			for ( LelProdList::Iter prod = lel->prodList; prod.lte(); prod++ ) {
				if ( !firstProd )
					out << "\n      | ";
				firstProd = false;
				
				/* Check if this is an empty production */
				if ( prod->prodElList == 0 || prod->prodElList->length() == 0 ) {
					out << "/* empty */";
				}
				else {
					/* Output each element in the production */
					bool firstEl = true;
					for ( ProdElList::Iter el = *prod->prodElList; el.lte(); el++ ) {
						if ( !firstEl )
							out << " ";
						firstEl = false;
						
						if ( el->langEl != 0 )
							writeLangElName( out, el->langEl );
					}
				}
			}
			
			out << "\n\n";
		}
	}
}
