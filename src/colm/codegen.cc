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
#include "fsmcodegen.h"

void FsmCodeGen::writeIncludes()
{
	out <<
		"#include <stdio.h>\n"
		"#include <stdlib.h>\n"
		"#include <string.h>\n"
		"#include <assert.h>\n"
		"\n"
		"#include <colm/pdarun.h>\n"
		"#include <colm/debug.h>\n"
		"#include <colm/bytecode.h>\n"
		"#include <colm/defs.h>\n"
		"#include <colm/input.h>\n"
		"#include <colm/tree.h>\n"
		"#include <colm/program.h>\n"
		"#include <colm/colm.h>\n"
		"\n";
}

void FsmCodeGen::writeMain( long activeRealm )
{
	out <<
		"int main( int argc, const char **argv )\n"
		"{\n"
		"\tstruct colm_program *prg;\n"
		"\tint exit_status;\n"
		"\tint i, j;\n"
		"\n"
		"\tprg = colm_new_program( &" << objectName << " );\n"
		"\n"
		"\t/* Debug options are consumed here so the program itself does not\n"
		"\t * see them. Everything else is passed through unchanged. */\n"
		"\tfor ( i = 1, j = 1; i < argc; i++ ) {\n"
		"\t\tif ( strcmp( argv[i], \"-h\" ) == 0 ||\n"
		"\t\t\t\tstrcmp( argv[i], \"-H\" ) == 0 ||\n"
		"\t\t\t\tstrcmp( argv[i], \"-?\" ) == 0 ||\n"
		"\t\t\t\tstrcmp( argv[i], \"--help\" ) == 0 ) {\n"
		"\t\t\tfprintf( stdout,\n"
		"\t\t\t\t\"usage: %s [options] [args]\\n\"\n"
		"\t\t\t\t\"general:\\n\"\n"
		"\t\t\t\t\"   -h, -H, -?, --help   print this usage and exit\\n\"\n"
		"\t\t\t\t\"   --dump-lexer         trace how input is tokenized\\n\"\n"
		"\t\t\t\t\"   --dump-parse         trace parser region decisions\\n\"\n"
		"\t\t\t\t\"   --dump-cst           dump the concrete syntax tree\\n\"\n"
		"\t\t\t\t\"   --dump-cst=TYPES     dump only the listed node types\\n\"\n"
		"\t\t\t\t\"                        (comma-separated exact names)\\n\"\n"
		"\t\t\t\t\"other arguments are passed to the program.\\n\",\n"
		"\t\t\t\targv[0] );\n"
		"\t\t\tcolm_delete_program( prg );\n"
		"\t\t\treturn 0;\n"
		"\t\t}\n"
		"\t\telse if ( strcmp( argv[i], \"--dump-lexer\" ) == 0 )\n"
		"\t\t\tprg->dump_lexer = 1;\n"
		"\t\telse if ( strcmp( argv[i], \"--dump-parse\" ) == 0 )\n"
		"\t\t\tprg->dump_parse = 1;\n"
		"\t\telse if ( strcmp( argv[i], \"--dump-cst\" ) == 0 )\n"
		"\t\t\tprg->dump_cst = 1;\n"
		"\t\telse if ( strncmp( argv[i], \"--dump-cst=\", 11 ) == 0 ) {\n"
		"\t\t\tprg->dump_cst = 1;\n"
		"\t\t\tprg->dump_cst_filter = argv[i] + 11;\n"
		"\t\t}\n"
		"\t\telse\n"
		"\t\t\targv[j++] = argv[i];\n"
		"\t}\n"
		"\targc = j;\n"
		"\n"
		"\tcolm_set_debug( prg, " << activeRealm << " );\n"
		"\tcolm_run_program( prg, argc, argv );\n"
		"\texit_status = colm_delete_program( prg );\n"
		"\treturn exit_status;\n"
		"}\n"
		"\n";

	out.flush();
}