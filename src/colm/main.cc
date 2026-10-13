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

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <stdio.h>
#include <stdbool.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>

#include "debug.h"
#include "global.h"
#include "pcheck.h"
#include "version.h"
#include "compiler.h"
#include "colm.h"

#if defined(CONS_INIT)
#include "consinit.h"
#elif defined(LOAD_INIT)
#include "loadinit.h"
#else
#include "loadfinal.h"
#endif

using std::istream;
using std::ifstream;
using std::ostream;
using std::ios;
using std::cin;
using std::cout;
using std::cerr;
using std::endl;

/* Graphviz dot file generation. */
bool genGraphviz = false;
bool genEbnf = false;

using std::ostream;
using std::istream;
using std::ifstream;
using std::ofstream;
using std::ios;
using std::cout;
using std::cerr;
using std::cin;
using std::endl;

InputLoc internal;

/* Io globals. */
istream *inStream = 0;
ostream *outStream = 0;
ostream *outLexSmStream = 0;
const char *inputFn = 0;
const char *inputFn2 = 0;
const char *outputFn = 0;
const char *intermedFn = 0;
const char *intermedLexDbgFn = 0;
const char *binaryFn = 0;
const char *exportHeaderFn = 0;
const char *exportCodeFn = 0;
const char *commitCodeFn = 0;
const char *fromBuildDir = 0;
const char *objectName = "colm_object";
bool exportCode = false;
bool hostAdapters = true;

bool generateGraphviz = false;
bool generateEbnf = false;

/* Parser state report. `--pda-report` dumps states; `--pda-report=conflicts`
 * prints grouped conflicts (with item detail); `--pda-report=clusters` prints
 * the grouped conflict index and cross-state shapes only; `--pda-report=json`
 * prints the same conflicts as JSON. `--pda-report=state=N` and
 * `--pda-report=token=T` restrict the output. Output defaults to stderr and
 * can be redirected with `--pda-report-file=FILE`. */
std::ostream *pdaReportStream = &std::cerr;
int pdaReportMode = PdaReportOff;
long pdaReportFilterState = -1;
const char *pdaReportFilterToken = 0;
/* Static so its destructor flushes the report at exit (a leaked pointer would
 * drop the buffered tail). */
static std::ofstream pdaReportFile;

/* Parse and analyze the grammar only. Skip code generation and the build.
 * Intended for grammar authoring/debugging. */
bool syntaxOnly = false;
/* Always-on static grammar diagnostics; --no-warn-grammar disables them. */
bool warnGrammar = true;
bool generatePdaReport = false;
bool dumpSql = false;
long dumpSqlGrammarId = 1;
bool dumpGlobals = false;
bool dumpLexer = false;
/* Dump each token region: index, declaration site and tokens. */
bool dumpRegions = false;
bool dumpCst = false;
/* Dump the reduced lexer state machine. Opt-in; default off. */
bool dumpLexerSm = false;
bool verbose = false;
bool logging = false;
bool branchPointInfo = false;
bool run = false;
/* Run the program in-process from the compiler-built runtime data, with no
 * code generation and no C compilation. */
bool interpret = false;
bool addUniqueEmptyProductions = false;
bool gblLibrary = false;
long gblActiveRealm = 0;
bool outputSpecifiedWithDashP = false;

ArgsVector includePaths;
ArgsVector libraryPaths;
DefineVector defineArgs;
ArgsVector additionalCodeFiles;

/* Print version information. */
void version();

/* Total error count. */
int gblErrorCount = 0;

// Provides a default for -B by detecting if we are running from the build
// location in the source tree. This will dictate compiler and linker args for
// compiling colm programs.
const char *defaultBuildDir();

/*
 * Alphabet Type for the parsing machinery. The trees/strings of parsed data
 * all use char type. Currently we can support signed char, unsigned char or
 * char. If changing this, the colm_alph_t type needs to change as well.
 * Currently, this is a compile time change only. A colm binary currently
 * connot be made to work with multiple alphabet types.
 */

/* The file name to report for a location. A location with no file has a null
 * file name, until it is copied. The InputLoc copy constructor, which we share
 * with ragel, turns the null into "-". Colm gives "-" no meaning as a file
 * name, so both forms mean no file. */
const char *locFileName( const InputLoc &loc )
{
	if ( loc.fileName == 0 || strcmp( loc.fileName, "-" ) == 0 )
		return "<input>";
	return loc.fileName;
}

/* Print the opening to an error in the input, then return the error ostream. */
ostream &error( const InputLoc &loc )
{
	/* Keep the error count. */
	gblErrorCount += 1;

	cerr << locFileName( loc ) << ":";

	if ( loc.line == -1 ) {
		cerr << "INT: ";
	}
	else {
		cerr << loc.line << ":" << loc.col << ": ";
	}
	return cerr;
}

/* Print the opening to a program error, then return the error stream. */
ostream &error()
{
	gblErrorCount += 1;
	cerr << "error: colm: ";
	return cerr;
}


/* Print the opening to a warning, then return the error ostream. */
ostream &warning( )
{
	cerr << "warning: " << inputFn << ": ";
	return cerr;
}

/* Print the opening to a warning in the input, then return the error ostream. */
ostream &warning( const InputLoc &loc )
{
	/* Use the location's own file, not the top-level input: productions may
	 * come from an included grammar file. */
	cerr << "warning: " << locFileName( loc ) << ":" <<
			loc.line << ":" << loc.col << ": ";
	return cerr;
}

void escapeLineDirectivePath( std::ostream &out, char *path )
{
	for ( char *pc = path; *pc != 0; pc++ ) {
		if ( *pc == '\\' )
			out << "\\\\";
		else
			out << *pc;
	}
}

void escapeLineDirectivePath( std::ostream &out, char *path );
void scan( char *fileName, istream &input );

bool printStatistics = false;

/* Print a summary of the options. */
void usage()
{
	cout <<
"usage: colm [options] file\n"
"general:\n"
"   -h, -H, -?, --help   print this usage and exit\n"
"   -v --version         print version information and exit\n"
"   -b <ident>           use <ident> as name of C object encapulaing the program\n"
"   -o <file>            if -c given, write C parse object to <file>,\n"
"                        otherwise write binary to <file>\n"
"   -p <file>            write C parse object to <file>\n"
"   -e <file>            write C++ export header to <file>\n"
"   -x <file>            write C++ export code to <file>\n"
"   -m <file>            write C++ commit code to <file>\n"
"   -a <file>            additional code file to include in output program\n"
"   -E N=V               set a string value available in the program\n"
"   -I <path>            additional include path for the compiler\n"
"   -i                   activate branchpoint information\n"
"   -L <path>            additional library path for the linker\n"
"   -l                   activate logging\n"
"   -r                   run output program and replace process\n"
"   -c                   compile only (don't produce binary)\n"
"   -V                   print dot format (graphiz)\n"
"   --interpret          directly interpret a colm program\n"
"   --ebnf               print EBNF for railroad diagram\n"
"   --dump-lexer.        dump lexer tokens\n"
"   --dump-regions       dump token regions: index, location and tokens\n"
"   --dump-cst  .        dump concrete syntax tree\n"
"   --dump-lexer-sm[=F]  dump reduced lexer state machine (to F, default\n"
"                        <output>.lex-sm.txt)\n"
"   --dump-sql[=N]      dump grammar as SQL (grammar id N, default 1)\n"
"   --dump-globals       print all globals\n"
"   --pda-report         print parser states\n"
"   --pda-report=conflicts\n"
"                        print grouped conflicts with item detail\n"
"   --pda-report=clusters\n"
"                        print grouped conflict index and shapes\n"
"   --pda-report=json    print conflicts as JSON\n"
"   --pda-report=state=N  restrict output to state N\n"
"   --pda-report=token=T  restrict output to token T\n"
"   --pda-report-file=F  write the report to file F (default stderr)\n"
"   --syntax-only        parse and analyze only; write no output, no build\n"
"   --no-warn-grammar    disable static grammar diagnostics\n"
"   -d                   print verbose debug information\n"
"   -B <path>\n"
"       Run Colm from the build directory. Use this when building from source\n"
"       and using the resulting binary without installing it. Colm will attempt\n"
"       to detect when it is run from the build directory. This flag lets the\n"
"       user be expliclit about it. The detection method is specific to the OS\n"
"       and can fail. The path given should be the root of the build directory,\n"
"       eg what would be returned by ABS_TOP_BUILDDIR (directory where src is).\n"
#if DEBUG
"   -D <tag>             print more information about <tag>\n"
"                        (BYTECODE|PARSE|MATCH|COMPILE|POOL|PRINT|INPUT|SCAN\n"
#endif
	;
}

/* Print version information. */
void version()
{
	cout << "Colm version " COLM_VERSION << " " COLM_PUBDATE << endl <<
			"Copyright (c) 2007-2026 by Dr. Adrian D. Thurston" << endl;
}

/* Scans a string looking for the file extension. If there is a file
 * extension then pointer returned points to inside the string
 * passed in. Otherwise returns null. */
const char *findFileExtension( const char *stemFile )
{
	const char *ppos = stemFile + strlen(stemFile) - 1;

	/* Scan backwards from the end looking for the first dot.
	 * If we encounter a '/' before the first dot, then stop the scan. */
	while ( 1 ) {
		/* If we found a dot or got to the beginning of the string then
		 * we are done. */
		if ( ppos == stemFile || *ppos == '.' )
			break;

		/* If we hit a / then there is no extension. Done. */
		if ( *ppos == '/' ) {
			ppos = stemFile;
			break;
		}
		ppos--;
	}

	/* If we got to the front of the string then bail we
	 * did not find an extension  */
	if ( ppos == stemFile )
		ppos = 0;

	return ppos;
}

/* Make a file name from a stem. Removes the old filename suffix and
 * replaces it with a new one. Returns a newed up string. */
char *fileNameFromStem( const char *stemFile, const char *suffix )
{
	int len = strlen( stemFile );
	assert( len > 0 );

	/* Get the extension. */
	const char *ppos = findFileExtension( stemFile );

	/* If an extension was found, then shorten what we think the len is. */
	if ( ppos != 0 )
		len = ppos - stemFile;

	int slen = suffix != 0 ? strlen( suffix ) : 0;
	char *retVal = new char[ len + slen + 1 ];
	strncpy( retVal, stemFile, len );
	if ( suffix != 0 )
		strcpy( retVal + len, suffix );
	retVal[len+slen] = 0;

	return retVal;
}

void openOutputCompiled()
{
	/* Start with the fn given by -o option. */
	binaryFn = outputFn;

	if ( binaryFn == 0 )
		binaryFn = fileNameFromStem( inputFn, 0 );

	if ( intermedFn == 0 )
		intermedFn = fileNameFromStem( binaryFn, ".c" );

	if ( dumpLexerSm && intermedLexDbgFn == 0 )
		intermedLexDbgFn = fileNameFromStem( binaryFn, ".lex-sm.txt" );

	if ( binaryFn != 0 && inputFn != 0 &&
			strcmp( inputFn, binaryFn  ) == 0 )
	{
		error() << "output file \"" << binaryFn  <<
				"\" is the same as the input file" << endl;
	}

	if ( intermedFn != 0 && inputFn != 0 &&
			strcmp( inputFn, intermedFn  ) == 0 )
	{
		error() << "intermediate file \"" << intermedFn  <<
				"\" is the same as the input file" << endl;
	}

	if ( intermedFn != 0 ) {
		/* Open the output stream, attaching it to the filter. */
		ofstream *outFStream = new ofstream( intermedFn );

		if ( !outFStream->is_open() ) {
			error() << "error opening " << intermedFn << " for writing" << endl;
			exit(1);
		}

		outStream = outFStream;
	}
	else {
		/* Writing out ot std out. */
		outStream = &cout;
	}
	if ( intermedLexDbgFn != 0 ) {
		/* Open the output stream, attaching it to the filter. */
		ofstream *outFStream = new ofstream( intermedLexDbgFn );

		if ( !outFStream->is_open() ) {
			error() << "error opening " << intermedLexDbgFn << " for writing" << endl;
			exit(1);
		}

		outLexSmStream = outFStream;
	}
}

void openOutputLibrary()
{
	if ( outputFn == 0 )
		outputFn = fileNameFromStem( inputFn, ".c" );

	/* Make sure we are not writing to the same file as the input file. */
	if ( outputFn != 0 && inputFn != 0 &&
			strcmp( inputFn, outputFn  ) == 0 )
	{
		error() << "output file \"" << outputFn  <<
				"\" is the same as the input file" << endl;
	}

	if ( outputFn != 0 ) {
		/* Open the output stream, attaching it to the filter. */
		ofstream *outFStream = new ofstream( outputFn );

		if ( !outFStream->is_open() ) {
			error() << "error opening " << outputFn << " for writing" << endl;
			exit(1);
		}

		outStream = outFStream;
	}
	else {
		/* Writing out ot std out. */
		outStream = &cout;
	}

	if ( dumpLexerSm && intermedLexDbgFn == 0 )
		intermedLexDbgFn = fileNameFromStem( outputFn, ".lex-sm.txt" );

	if ( intermedLexDbgFn != 0 ) {
		ofstream *outFStream = new ofstream( intermedLexDbgFn );

		if ( !outFStream->is_open() ) {
			error() << "error opening " << intermedLexDbgFn << " for writing" << endl;
			exit(1);
		}

		outLexSmStream = outFStream;
	}
}

/* Open just the lexer state machine dump stream. Used when we are not opening
 * the compiled or library output at all (--syntax-only), but still want
 * --dump-lexer-sm to produce its file. */
void openLexerSmOutput( const char *stem )
{
	if ( dumpLexerSm && intermedLexDbgFn == 0 && stem != 0 )
		intermedLexDbgFn = fileNameFromStem( stem, ".lex-sm.txt" );

	if ( intermedLexDbgFn != 0 ) {
		ofstream *outFStream = new ofstream( intermedLexDbgFn );

		if ( !outFStream->is_open() ) {
			error() << "error opening " << intermedLexDbgFn << " for writing" << endl;
			exit(1);
		}

		outLexSmStream = outFStream;
	}
}

void openExports( )
{
	/* Make sure we are not writing to the same file as the input file. */
	if ( inputFn != 0 && exportHeaderFn != 0 && strcmp( inputFn, exportHeaderFn  ) == 0 ) {
		error() << "output file \"" << exportHeaderFn  <<
				"\" is the same as the input file" << endl;
	}

	if ( exportHeaderFn != 0 ) {
		/* Open the output stream, attaching it to the filter. */
		ofstream *outFStream = new ofstream( exportHeaderFn );

		if ( !outFStream->is_open() ) {
			error() << "error opening " << exportHeaderFn << " for writing" << endl;
			exit(1);
		}

		outStream = outFStream;
	}
	else {
		/* Writing out ot std out. */
		outStream = &cout;
	}
}

void openExportsImpl( )
{
	/* Make sure we are not writing to the same file as the input file. */
	if ( inputFn != 0 && exportCodeFn != 0 && strcmp( inputFn, exportCodeFn  ) == 0 ) {
		error() << "output file \"" << exportCodeFn  <<
				"\" is the same as the input file" << endl;
	}

	if ( exportCodeFn != 0 ) {
		/* Open the output stream, attaching it to the filter. */
		ofstream *outFStream = new ofstream( exportCodeFn );

		if ( !outFStream->is_open() ) {
			error() << "error opening " << exportCodeFn << " for writing" << endl;
			exit(1);
		}

		outStream = outFStream;
	}
	else {
		/* Writing out ot std out. */
		outStream = &cout;
	}
}

void openCommit( )
{
	/* Make sure we are not writing to the same file as the input file. */
	if ( inputFn != 0 && commitCodeFn != 0 && strcmp( inputFn, commitCodeFn  ) == 0 ) {
		error() << "output file \"" << commitCodeFn  <<
				"\" is the same as the input file" << endl;
	}

	if ( commitCodeFn != 0 ) {
		/* Open the output stream, attaching it to the filter. */
		ofstream *outFStream = new ofstream( commitCodeFn );

		if ( !outFStream->is_open() ) {
			error() << "error opening " << commitCodeFn << " for writing" << endl;
			exit(1);
		}

		outStream = outFStream;
	}
	else {
		/* Writing out ot std out. */
		outStream = &cout;
	}
}

int compileOutputCommand( const char *command )
{
	if ( verbose )
		cout << "compiling with: '" << command << "'" << endl;
	int res = system( command );
	if ( res != 0 )
		error() << "there was a problem compiling the output" << endl;

	return res;
}

void runOutputProgram()
{
	if ( verbose )
		cout << "running output: '" << binaryFn << "'" << endl;

	execl( binaryFn, binaryFn, NULL );
	/* We shall never return here! */
}

void compileOutput()
{
	const char *compiler = getenv( "CC" );
	if ( compiler == 0 )
		compiler = "gcc";

	const char *cflags = getenv( "CFLAGS" );
	if ( cflags == 0 )
		cflags = "";

	std::ostringstream command;

	if ( fromBuildDir != 0 ) {
		command << fromBuildDir << "/libtool --tag=CC --mode=link "
		        << compiler << " -Wall -Wwrite-strings"
		        << " -g " << cflags
		        << " -o " << binaryFn
		        << " " << intermedFn
		        << " -I" << fromBuildDir << "/src/colm/include"
		        << " -static"
		        << " " << fromBuildDir << "/src/colm/libcolm.la";
	}
	else {
		command << compiler << " -Wall -Wwrite-strings"
		        << " -g " << cflags
		        << " -o " << binaryFn
		        << " " << intermedFn
		        << " -I" << INCLUDEDIR
		        << " -L" << LIBDIR
		        << " -Wl,-rpath," << LIBDIR;
	}

	for ( ArgsVector::Iter af = additionalCodeFiles; af.lte(); af++ ) {
		command << " " << *af;
	}
	for ( ArgsVector::Iter ip = includePaths; ip.lte(); ip++ ) {
		command << " -I" << *ip;
	}
	for ( ArgsVector::Iter lp = libraryPaths; lp.lte(); lp++ ) {
		command << " -L" << *lp;
	}

	if ( fromBuildDir == 0 )
		command << " -lcolm";

	std::string commandStr = command.str();
	if( !compileOutputCommand( commandStr.c_str() ) && run )
		runOutputProgram();
}

void processArgs( int argc, const char **argv )
{
	ParamCheck pc( "p:cD:e:x:I:L:vdliro:S:M:vHh?-:sVa:m:b:E:B:", argc, argv );

	while ( pc.check() ) {
		switch ( pc.state ) {
		case ParamCheck::match:
			switch ( pc.parameter ) {
			case 'I':
				includePaths.append( pc.parameterArg );
				break;
			case 'v':
				version();
				exit(0);
				break;
			case 'd':
				verbose = true;
				break;
			case 'l':
				logging = true;
				break;
			case 'L':
				libraryPaths.append( pc.parameterArg );
				break;
			case 'i':
				branchPointInfo = true;
				break;
			case 'r':
				run = true;
				break;
			case 'p':
				outputSpecifiedWithDashP = true;
				/* fallthrough */
			case 'o':
				/* Output. */
				if ( *pc.parameterArg == 0 )
					error() << "a zero length output file name was given" << endl;
				else if ( outputFn != 0 )
					error() << "more than one output file name was given" << endl;
				else {
					/* Ok, remember the output file name. */
					outputFn = pc.parameterArg;
				}
				break;

			case 'b':
				/* object name. */
				if ( *pc.parameterArg == 0 )
					error() << "a zero length object name was given" << endl;
				else {
					/* Ok, remember the output file name. */
					objectName = pc.parameterArg;
					hostAdapters = false;
				}
				break;

			case 'H': case 'h': case '?':
				usage();
				exit(0);
			case 's':
				printStatistics = true;
				break;
			case 'V':
				generateGraphviz = true;
				break;
			case '-':
				if ( strcasecmp(pc.parameterArg, "help") == 0 ) {
					usage();
					exit(0);
				}
				else if ( strcasecmp(pc.parameterArg, "version") == 0 ) {
					version();
					exit(0);
				}
				else if ( strcasecmp(pc.parameterArg, "ebnf") == 0 ) {
					generateEbnf = true;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "pda-report") == 0 ) {
					generatePdaReport = true;
					pdaReportMode = PdaReportFull;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "pda-report=conflicts") == 0 ) {
					generatePdaReport = true;
					pdaReportMode = PdaReportConflicts;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "pda-report=clusters") == 0 ) {
					generatePdaReport = true;
					pdaReportMode = PdaReportClusters;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "pda-report=json") == 0 ) {
					generatePdaReport = true;
					pdaReportMode = PdaReportJson;
					break;
				}
				else if ( strncasecmp(pc.parameterArg, "pda-report=state=", 17) == 0 ) {
					generatePdaReport = true;
					pdaReportFilterState = atol( pc.parameterArg + 17 );
					break;
				}
				else if ( strncasecmp(pc.parameterArg, "pda-report=token=", 17) == 0 ) {
					generatePdaReport = true;
					pdaReportFilterToken = pc.parameterArg + 17;
					break;
				}
				else if ( strncasecmp(pc.parameterArg, "pda-report-file=", 16) == 0 ) {
					pdaReportFile.open( pc.parameterArg + 16, std::ios::out | std::ios::trunc );
					if ( pdaReportFile.is_open() )
						pdaReportStream = &pdaReportFile;
					else
						error() << "failed to open pda report file: "
								<< ( pc.parameterArg + 16 ) << "\n";
					generatePdaReport = true;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "syntax-only") == 0 ) {
					syntaxOnly = true;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "interpret") == 0 ) {
					interpret = true;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "no-warn-grammar") == 0 ) {
					warnGrammar = false;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "dump-globals") == 0 ) {
					dumpGlobals = true;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "dump-lexer") == 0 ) {
					dumpLexer = true;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "dump-regions") == 0 ) {
					dumpRegions = true;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "dump-cst") == 0 ) {
					dumpCst = true;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "dump-lexer-sm") == 0 ) {
					dumpLexerSm = true;
					break;
				}
				else if ( strncasecmp(pc.parameterArg, "dump-lexer-sm=", 14) == 0 ) {
					dumpLexerSm = true;
					intermedLexDbgFn = pc.parameterArg + 14;
					break;
				}
				else if ( strcasecmp(pc.parameterArg, "dump-sql") == 0 ) {
					dumpSql = true;
					break;
				}
				else if ( strncasecmp(pc.parameterArg, "dump-sql=", 9) == 0 ) {
					dumpSql = true;
					dumpSqlGrammarId = atol( pc.parameterArg + 9 );
					break;
				}
				else {
					error() << "--" << pc.parameterArg <<
							" is an invalid argument" << endl;
				}
				break;
			case 'c':
				gblLibrary = true;
				break;
			case 'e':
				exportHeaderFn = pc.parameterArg;
				break;
			case 'x':
				exportCodeFn = pc.parameterArg;
				break;
			case 'a':
				additionalCodeFiles.append( pc.parameterArg );
				break;
			case 'm':
				commitCodeFn = pc.parameterArg;
				break;
			case 'B':
				fromBuildDir = pc.parameterArg;
				break;

			case 'E': {
				const char *eq = strchr( pc.parameterArg, '=' );
				if ( eq == 0 )
					fatal( "-E option argument must contain =" );
				if ( eq == pc.parameterArg )
					fatal( "-E variable name is of zero length" );

				defineArgs.append( DefineArg(
						String( pc.parameterArg, eq-pc.parameterArg ),
						String( eq + 1 ) ) );

				break;
			}

			case 'D':
#if DEBUG
				// @NOTE: keep this in sync with 'debug.c': 'colm_realm_names'
				if ( strcmp( pc.parameterArg, colm_realm_names[0] ) == 0 )
					gblActiveRealm |= REALM_BYTECODE;
				else if ( strcmp( pc.parameterArg, colm_realm_names[1] ) == 0 )
					gblActiveRealm |= REALM_PARSE;
				else if ( strcmp( pc.parameterArg, colm_realm_names[2] ) == 0 )
					gblActiveRealm |= REALM_MATCH;
				else if ( strcmp( pc.parameterArg, colm_realm_names[3] ) == 0 )
					gblActiveRealm |= REALM_COMPILE;
				else if ( strcmp( pc.parameterArg, colm_realm_names[4] ) == 0 )
					gblActiveRealm |= REALM_POOL;
				else if ( strcmp( pc.parameterArg, colm_realm_names[5] ) == 0 )
					gblActiveRealm |= REALM_PRINT;
				else if ( strcmp( pc.parameterArg, colm_realm_names[6] ) == 0 )
					gblActiveRealm |= REALM_INPUT;
				else if ( strcmp( pc.parameterArg, colm_realm_names[7] ) == 0 )
					gblActiveRealm |= REALM_SCAN;
				else
					fatal( "unknown argument to -D %s\n", pc.parameterArg );
#else
				fatal( "-D option specified but debugging messages not compiled in\n" );
#endif
				break;

			}
			break;

		case ParamCheck::invalid:
			error() << "-" << pc.parameter << " is an invalid argument" << endl;
			break;

		case ParamCheck::noparam:
			/* It is interpreted as an input file. */
			if ( *pc.curArg == 0 )
				error() << "a zero length input file name was given" << endl;
			else if ( inputFn != 0 ) {
                            if ( interpret &&  inputFn2 == 0) inputFn2 = pc.curArg;
                            else error() << "more than one input file name was given" << endl;
			} else {
				/* OK, Remember the filename. */
				inputFn = pc.curArg;
			}
			break;
		}
	}
}

bool readCheck( const char *fn )
{
	int result = true;

	/* Check if we can open the input file for reading. */
	ifstream *inFile = new ifstream( fn );
	if ( ! inFile->is_open() )
		result = false;

	delete inFile;
	return result;
}

/* Main, process args and call yyparse to start scanning input. */
int main(int argc, const char **argv)
{
	processArgs( argc, argv );

	if ( fromBuildDir == 0 )
		fromBuildDir = defaultBuildDir();

	if ( verbose )
		gblActiveRealm = 0xffffffff;

	/* Bail on above errors. */
	if ( gblErrorCount > 0 )
		exit(1);

	/* Make sure we are not writing to the same file as the input file. */
	if ( inputFn != 0 && outputFn != 0 &&
			strcmp( inputFn, outputFn  ) == 0 )
	{
		error() << "output file \"" << outputFn  <<
				"\" is the same as the input file" << endl;
	}

#if defined(LOAD_INIT) || defined(LOAD_COLM)
	/* Open the input file for reading. */
	if ( inputFn == 0 ) {
		error() << "colm: no input file given" << endl;
	}
	else {
		/* Check if we can open the input file for reading. */
		if ( ! readCheck( inputFn ) )
			error() << "could not open " << inputFn << " for reading" << endl;
	}
#endif

	if ( !gblLibrary && outputSpecifiedWithDashP ) {
		error() << "-p option must be used with -c" << endl;
	}


	/* Bail on above errors. */
	if ( gblErrorCount > 0 )
		exit(1);

	Compiler *pd = new Compiler;

#if defined(CONS_INIT)
	BaseParser *parser = new ConsInit( pd );
#elif defined(LOAD_INIT)
	BaseParser *parser = new LoadInit( pd, inputFn );
#else
	BaseParser *parser = consLoadColm( pd, inputFn );
#endif

	parser->go( gblActiveRealm );

	/* Parsing complete, check for errors.. */
	if ( gblErrorCount > 0 )
		return 1;

	/* Initiate a compile following a parse. */
	pd->compile();

	if ( pdaReportFile.is_open() )
		pdaReportFile.flush();

	/*
	 * Write output.
	 */
	if ( generateGraphviz ) {
		outStream = &cout;
		pd->writeDotFile();
	}
	else if ( generateEbnf ) {
		outStream = &cout;
		pd->writeEbnfFile();
	}
	else if ( dumpSql ) {
		outStream = &cout;
		pd->writeSqlFile();
	}
	else if ( dumpGlobals ) {
		pd->dumpGlobals();
	}
	else if ( dumpRegions ) {
		pd->dumpRegions();
	}
	else if ( interpret ) {
		/* Run the program in-process from the compiler-built runtime data.
		 * This needs no code generation and no C compilation: the compiler's
		 * runtimeData already carries the fully built fsm_tables, pda_tables
		 * and the internal executor hooks. */
		struct colm_program *prg = colm_new_program( pd->runtimeData );

		colm_set_debug( prg, gblActiveRealm );
		prg->dump_lexer = dumpLexer ? 1 : 0;
		prg->dump_cst = dumpCst ? 1 : 0;

		/* Present the input file as argv[0], as a compiled program would. */
                const char *iargv[3] = {};
		iargv[0] = inputFn;
                if ( inputFn2 ) iargv[1] = inputFn2;
		colm_run_program( prg, inputFn2 ? 2 : 1, iargv );

		int exit_status = colm_delete_program( prg );
		delete parser;
		delete pd;
		return exit_status;
	}
	else if ( syntaxOnly ) {
		/* Parse and analyze only. No code generation, no build. The lexer
		 * state machine is reduced during analysis, so honor --dump-lexer-sm
		 * here even though we skip all output. */
		if ( dumpLexerSm ) {
			openLexerSmOutput( outputFn != 0 ? outputFn : inputFn );
			if ( outLexSmStream != 0 ) {
				pd->dumpLexerSm();
				delete outLexSmStream;
			}
		}
	}
	else {
		if ( gblLibrary )
			openOutputLibrary();
		else
			openOutputCompiled();

		pd->generateOutput( gblActiveRealm, ( commitCodeFn == 0 ) );
		if ( outStream != 0 )
			delete outStream;
		if ( outLexSmStream != 0 )
			delete outLexSmStream;

		if ( !gblLibrary )
			compileOutput();

		if ( exportHeaderFn != 0 ) {
			openExports();
			pd->generateExports();
			delete outStream;
		}
		if ( exportCodeFn != 0 ) {
			openExportsImpl();
			pd->generateExportsImpl();
			delete outStream;
		}
		if ( commitCodeFn != 0 ) {
			openCommit();
			pd->writeCommit();
			delete outStream;
		}
	}

	delete parser;
	delete pd;

	/* Bail on above errors. */
	if ( gblErrorCount > 0 )
		exit(1);

	return 0;
}
