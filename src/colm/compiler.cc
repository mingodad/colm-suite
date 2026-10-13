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

#include "compiler.h"

#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <unistd.h>
#include <assert.h>
#include <iostream>

#include "parsetree.h"
#include "pdacodegen.h"
#include "fsmcodegen.h"
#include "colm.h"

using std::ostringstream;
using std::cout;
using std::cerr;
using std::endl;

char machineMain[] = "main";
exit_object endp;
void operator<<( ostream &out, exit_object & )
{
	out << endl;
	exit(1);
}

/*
 * The scanner alphabet. The parsing machinery uses char data throughout, so
 * this is fixed at compile time; changing it requires changing colm_alph_t
 * as well. It is unsigned, so keys run 0..255 and the characters of a
 * pattern are read through unsigned char to agree with the runtime, where
 * the input is unsigned char too.
 */
const AlphType colmAlphType = { "unsigned", "char", false, 0, UCHAR_MAX, sizeof(unsigned char) };

Key makeFsmKeyHex( char *str, const InputLoc &loc, Compiler *pd )
{
	/* Reset errno so we can check for overflow or underflow. In the event of
	 * an error, sets the return val to the upper or lower bound being tested
	 * against. */
	errno = 0;
	unsigned int size = colmAlphType.size;
	bool unusedBits = size < sizeof(unsigned long);

	unsigned long ul = strtoul( str, 0, 16 );


	if ( errno == ERANGE || (unusedBits && ul >> (size * 8)) ) {
		error(loc) << "literal " << str << " overflows the alphabet type" << endl;
		ul = 1 << (size * 8);
	}

	if ( colmAlphType.isSigned && unusedBits && ul >> (size * 8 - 1) )
		ul |= (ULONG_MAX >> (size*8 ) ) << (size*8);

	return Key( (long)ul );
}

Key makeFsmKeyDec( char *str, const InputLoc &loc, Compiler *pd )
{
	/* Convert the number to a decimal. First reset errno so we can check
	 * for overflow or underflow. */
	errno = 0;
	long long minVal = colmAlphType.minVal;
	long long maxVal = colmAlphType.maxVal;

	long long ll = strtoll( str, 0, 10 );

	/* Check for underflow. */
	if ( (errno == ERANGE && ll < 0) || ll < minVal) {
		error(loc) << "literal " << str << " underflows the alphabet type" << endl;
		ll = minVal;
	}
	/* Check for overflow. */
	else if ( (errno == ERANGE && ll > 0) || ll > maxVal ) {
		error(loc) << "literal " << str << " overflows the alphabet type" << endl;
		ll = maxVal;
	}

	return Key( (long)ll );
}

/* Make an fsm key in int format (what the fsm graph uses) from an alphabet
 * number returned by the parser. Validates that the number doesn't overflow
 * the alphabet type. */
Key makeFsmKeyNum( char *str, const InputLoc &loc, Compiler *pd )
{
	/* Switch on hex/decimal format. */
	if ( str[0] == '0' && str[1] == 'x' )
		return makeFsmKeyHex( str, loc, pd );
	else
		return makeFsmKeyDec( str, loc, pd );
}

/* Make an fsm int format (what the fsm graph uses) from a single character.
 * The alphabet is unsigned, so a character with the high bit set becomes a
 * key in 128..255 rather than a negative one. */
Key makeFsmKeyChar( char c, Compiler *pd )
{
	return Key( (unsigned char)c );
}

/* Make an fsm key array in int format (what the fsm graph uses) from a string
 * of characters, converting each as makeFsmKeyChar does. */
void makeFsmKeyArray( Key *result, char *data, int len, Compiler *pd )
{
	for ( int i = 0; i < len; i++ )
		result[i] = makeFsmKeyChar( data[i], pd );
}

/* Like makeFsmKeyArray except the result has only unique keys. They ordering
 * will be changed. */
void makeFsmUniqueKeyArray( KeySet &result, char *data, int len,
		bool caseInsensitive, Compiler *pd )
{
	for ( int si = 0; si < len; si++ ) {
		Key key = makeFsmKeyChar( data[si], pd );
		result.insert( key );
		if ( caseInsensitive ) {
			if ( key.isLower() )
				result.insert( key.toUpper() );
			else if ( key.isUpper() )
				result.insert( key.toLower() );
		}
	}
}

/* Make a builtin type. Depends on the signed nature of the alphabet type. */
FsmAp *makeBuiltin( BuiltinMachine builtin, Compiler *pd )
{
	FsmCtx *ctx = pd->fsmCtx;

	/* FsmAp created to return. */
	FsmAp *retFsm = 0;

	switch ( builtin ) {
	case BT_Any: {
		/* All characters. */
		retFsm = FsmAp::dotFsm( ctx );
		break;
	}
	case BT_Ascii: {
		/* Ascii characters 0 to 127. */
		retFsm = FsmAp::rangeFsm( ctx, 0, 127 );
		break;
	}
	case BT_Extend: {
		/* Ascii extended characters. This is the full byte range, the same
		 * machine as any. */
		retFsm = FsmAp::rangeFsm( ctx, 0, 255 );
		break;
	}
	case BT_Alpha: {
		/* Alpha [A-Za-z]. */
		FsmAp *upper = FsmAp::rangeFsm( ctx, 'A', 'Z' );
		FsmAp *lower = FsmAp::rangeFsm( ctx, 'a', 'z' );
		retFsm = FsmAp::unionOp( upper, lower );
		break;
	}
	case BT_Digit: {
		/* Digits [0-9]. */
		retFsm = FsmAp::rangeFsm( ctx, '0', '9' );
		break;
	}
	case BT_Alnum: {
		/* Alpha numerics [0-9A-Za-z]. */
		FsmAp *digit = FsmAp::rangeFsm( ctx, '0', '9' );
		FsmAp *upper = FsmAp::rangeFsm( ctx, 'A', 'Z' );
		FsmAp *lower = FsmAp::rangeFsm( ctx, 'a', 'z' );
		retFsm = FsmAp::unionOp( digit, upper, false );
		retFsm = FsmAp::unionOp( retFsm, lower );
		break;
	}
	case BT_Lower: {
		/* Lower case characters. */
		retFsm = FsmAp::rangeFsm( ctx, 'a', 'z' );
		break;
	}
	case BT_Upper: {
		/* Upper case characters. */
		retFsm = FsmAp::rangeFsm( ctx, 'A', 'Z' );
		break;
	}
	case BT_Cntrl: {
		/* Control characters. */
		FsmAp *cntrl = FsmAp::rangeFsm( ctx, 0, 31 );
		FsmAp *highChar = FsmAp::concatFsm( ctx, 127 );
		retFsm = FsmAp::unionOp( cntrl, highChar );
		break;
	}
	case BT_Graph: {
		/* Graphical ascii characters [!-~]. */
		retFsm = FsmAp::rangeFsm( ctx, '!', '~' );
		break;
	}
	case BT_Print: {
		/* Printable characters. Same as graph except includes space. */
		retFsm = FsmAp::rangeFsm( ctx, ' ', '~' );
		break;
	}
	case BT_Punct: {
		/* Punctuation. */
		FsmAp *range1 = FsmAp::rangeFsm( ctx, '!', '/' );
		FsmAp *range2 = FsmAp::rangeFsm( ctx, ':', '@' );
		FsmAp *range3 = FsmAp::rangeFsm( ctx, '[', '`' );
		FsmAp *range4 = FsmAp::rangeFsm( ctx, '{', '~' );
		retFsm = FsmAp::unionOp( range1, range2, false );
		retFsm = FsmAp::unionOp( retFsm, range3, false );
		retFsm = FsmAp::unionOp( retFsm, range4 );
		break;
	}
	case BT_Space: {
		/* Whitespace: [\t\v\f\n\r ]. */
		FsmAp *cntrl = FsmAp::rangeFsm( ctx, '\t', '\r' );
		FsmAp *space = FsmAp::concatFsm( ctx, ' ' );
		retFsm = FsmAp::unionOp( cntrl, space );
		break;
	}
	case BT_Xdigit: {
		/* Hex digits [0-9A-Fa-f]. */
		FsmAp *digit = FsmAp::rangeFsm( ctx, '0', '9' );
		FsmAp *upper = FsmAp::rangeFsm( ctx, 'A', 'F' );
		FsmAp *lower = FsmAp::rangeFsm( ctx, 'a', 'f' );
		retFsm = FsmAp::unionOp( digit, upper, false );
		retFsm = FsmAp::unionOp( retFsm, lower );
		break;
	}
	case BT_Lambda: {
		retFsm = FsmAp::lambdaFsm( ctx );
		break;
	}
	case BT_Empty: {
		retFsm = FsmAp::emptyFsm( ctx );
		break;
	}}

	return retFsm;
}

/*
 * Compiler
 */

/* Initialize the structure that will collect info during the parse of a
 * machine. */
Compiler::Compiler( )
:
	fsmGbl(new FsmGbl),
	fsmCtx(new FsmCtx( fsmGbl )),
	actionList(fsmCtx->actionList),
	nextNameId(0),
	getKeyExpr(0),
	accessExpr(0),
	curStateExpr(0),
	errorCount(0),
	nextEpsilonResolvedLink(0),
	nextTokenId(1),
	rootCodeBlock(0),
	mainReturnUT(0),
	//access(0),
	//tokenStruct(0),

	ptrLangEl(0),
	strLangEl(0),
	anyLangEl(0),
	rootLangEl(0),
	noTokenLangEl(0),
	eofLangEl(0),
	errorLangEl(0),
	ignoreLangEl(0),

	firstNonTermId(0),
	prodIdIndex(0),

	global(0),
	globalSel(0),
	globalObjectDef(0),
	arg0(0),
	argv(0),

	stream(0),
	inputSel(0),
	streamSel(0),

	uniqueTypeNil(0),
	uniqueTypePtr(0),
	uniqueTypeBool(0),
	uniqueTypeInt(0),
	uniqueTypeStr(0),
	uniqueTypeIgnore(0),
	uniqueTypeAny(0),
	uniqueTypeInput(0),
	uniqueTypeStream(0),
	nextPatConsId(0),
	nextGenericId(1),
	nextFuncId(0),
	nextHostId(0),
	nextObjectId(1),     /* 0 is  reserved for no object. */
	nextFrameId(0),
	nextParserId(0),
	revertOn(true),
	reducer(0),
	predValue(0),
	nextMatchEndNum(0),
	pdaShiftReduceConflicts(0),
	pdaReduceReduceConflicts(0),
	pdaResolvedConflicts(0),
	pdaRemainingShiftReduce(0),
	pdaRemainingReduceReduce(0),
	pdaPrecedenceTies(0),
	pdaResolvedByLevel(0),
	pdaResolvedByAssoc(0),
	pdaResolvedNonassoc(0),
	argvTypeRef(0),
	inContiguous(false),
	contiguousOffset(0),
	contiguousStretch(0)
{
}

/* Clean up the data collected during a parse. */
Compiler::~Compiler()
{
	/* Delete all the nodes in the action list. Will cause all the
	 * string data that represents the actions to be deallocated. Every
	 * action is a LexAction, delete through that type. */
	while ( actionList.head != 0 )
		delete LexAction::cast( actionList.detachFirst() );

	delete reducer;
	delete fsmCtx;
	delete fsmGbl;

	for ( CharVectVect::Iter fns = streamFileNames; fns.lte(); fns++ ) {
		const char **ptr = *fns;
		while ( *ptr != 0 ) {
			::free( (void*)*ptr );
			ptr += 1;
		}
		free( (void*) *fns );
	}
}

ostream &operator<<( ostream &out, const Token &token )
{
	out << token.data;
	return out;
}

NameInst **Compiler::makeNameIndex()
{
	/* The number of nodes in the tree can now be given by nextNameId. Put a
	 * null pointer on the end of the list to terminate it. */
	NameInst **nameIndex = new NameInst*[nextNameId+1];
	memset( nameIndex, 0, sizeof(NameInst*)*(nextNameId+1) );

	for ( NameVect::Iter ni = nameInstList; ni.lte(); ni++ )
		nameIndex[(*ni)->id] = *ni;

	return nameIndex;
}

void Compiler::createBuiltin( const char *name, BuiltinMachine builtin )
{
	LexExpression *expression = LexExpression::cons( builtin );
	LexJoin *join = LexJoin::cons( expression );
	LexDefinition *varDef = new LexDefinition( name, join );
	GraphDictEl *graphDictEl = new GraphDictEl( name, varDef );
	rootNamespace->rlMap.insert( graphDictEl );
}

/* Initialize the graph dict with builtin types. */
void Compiler::initGraphDict( )
{
	createBuiltin( "any", BT_Any );
	createBuiltin( "ascii", BT_Ascii );
	createBuiltin( "extend", BT_Extend );
	createBuiltin( "alpha", BT_Alpha );
	createBuiltin( "digit", BT_Digit );
	createBuiltin( "alnum", BT_Alnum );
	createBuiltin( "lower", BT_Lower );
	createBuiltin( "upper", BT_Upper );
	createBuiltin( "cntrl", BT_Cntrl );
	createBuiltin( "graph", BT_Graph );
	createBuiltin( "print", BT_Print );
	createBuiltin( "punct", BT_Punct );
	createBuiltin( "space", BT_Space );
	createBuiltin( "xdigit", BT_Xdigit );
	createBuiltin( "null", BT_Lambda );
	createBuiltin( "zlen", BT_Lambda );
	createBuiltin( "empty", BT_Empty );
}

/* Initialize the key operators object that will be referenced by all fsms
 * created. Keys are signed with the bounds of the alphabet type: this is the
 * comparison colm's scanners have always used. Minimization happens after
 * every operation that ends a sequence and once more when the graph is
 * finished. */
void Compiler::initKeyOps( )
{
	fsmCtx->keyOps->isSigned = colmAlphType.isSigned;
	fsmCtx->keyOps->minKey = Key( (long)colmAlphType.minVal );
	fsmCtx->keyOps->maxKey = Key( (long)colmAlphType.maxVal );

	fsmCtx->minimizeLevel = MinimizePartition2;
	fsmCtx->minimizeOpt = MinimizeMostOps;
}

/* Report a failed state machine operation. */
void Compiler::fsmFailure( const InputLoc &loc, const FsmRes &res )
{
	switch ( res.type ) {
		case FsmRes::TypeTooManyStates:
			error(loc) << "state machine has too many states" << endp;
			break;
		case FsmRes::TypePriorInteraction:
			error(loc) << "priority interaction in state machine" << endp;
			break;
		case FsmRes::TypeCondCostTooHigh:
			error(loc) << "condition cost too high in state machine" << endp;
			break;
		default:
			error(loc) << "internal error building state machine" << endp;
			break;
	}
}

Action *Compiler::newAction( const String &name, InlineList *inlineList )
{
	InputLoc loc;
	loc.line = 1;
	loc.col = 1;
	loc.fileName = 0;

	Action *action = new LexAction( loc, name, inlineList );
	actionList.append( action );
	return action;
}

void Compiler::initLongestMatchData()
{
	if ( regionSetList.length() > 0 ) {
		/* The initActId action gives act a default value. */
		InlineList *il4 = new InlineList;
		il4->append( new InlineItem( InputLoc(), InlineItem::LmInitAct ) );
		initActId = newAction( "initact", il4 );
		initActId->isLmAction = true;

		/* The setTokStart action sets tokstart. */
		InlineList *il5 = new InlineList;
		il5->append( new InlineItem( InputLoc(), InlineItem::LmSetTokStart ) );
		setTokStart = newAction( "tokstart", il5 );
		setTokStart->isLmAction = true;

		/* The setTokEnd action sets tokend. */
		InlineList *il3 = new InlineList;
		il3->append( new InlineItem( InputLoc(), InlineItem::LmSetTokEnd ) );
		setTokEnd = newAction( "tokend", il3 );
		setTokEnd->isLmAction = true;

		/* The action will also need an ordering: ahead of all user action
		 * embeddings. */
		initActIdOrd = fsmCtx->curActionOrd++;
		setTokStartOrd = fsmCtx->curActionOrd++;
		setTokEndOrd = fsmCtx->curActionOrd++;
	}
}

void Compiler::finishGraphBuild( FsmAp *graph )
{
	/* Resolve any labels that point to multiple states. Any labels that are
	 * still around are referenced only by gotos and calls and they need to be
	 * made into deterministic entry points. */
	graph->deterministicEntry();

	/*
	 * All state construction is now complete.
	 */

	/* Transfer global error actions. */
	for ( StateList::Iter state = graph->stateList; state.lte(); state++ )
		graph->transferErrorActions( state, 0 );

	graph->removeActionDups();

	/* Remove unreachable states. There should be no dead end states. The
	 * subtract and intersection operators are the only places where they may
	 * be created and those operators clean them up. */
	graph->removeUnreachableStates();

	/* No more fsm operations are to be done. Action ordering numbers are
	 * no longer of use and will just hinder minimization. Clear them. */
	graph->nullActionKeys();

	/* Transition priorities are no longer of use. We can clear them
	 * because they will just hinder minimization as well. Clear them. */
	graph->clearAllPriorities();

	/* Minimize here even if we minimized at every op. Now that function
	 * keys have been cleared we may get a more minimal fsm. */
	graph->minimizePartition2();
	graph->compressTransitions();
}

/* Build the name tree and supporting data structures. */
void Compiler::makeNameTree()
{
	/* Create the root name. */
	nextNameId = 1;

	/* First make the name tree. */
	for ( RegionImplList::Iter rel = regionImplList; rel.lte(); rel++ ) {
		/* Recurse on the instance. */
		rel->makeNameTree( rel->loc, this );
	}
}

FsmAp *Compiler::makeAllRegions()
{
	/* Build the name tree and supporting data structures. */
	makeNameTree();
	fsmCtx->nameIndex = makeNameIndex();

	int numGraphs = 0;
	FsmAp **graphs = new FsmAp*[regionImplList.length()];

	/* Make all the instantiations, we know that main exists in this list. */
	for ( RegionImplList::Iter rel = regionImplList; rel.lte(); rel++ ) {
		/* Build the graph from a walk of the parse tree. */
		FsmRes res = rel->walk( this );
		if ( !res.success() )
			fsmFailure( rel->loc, res );

		/* Wrap up the construction. */
		finishGraphBuild( res.fsm );

		/* Save off the new graph. */
		graphs[numGraphs++] = res.fsm;
	}

	/* NOTE: If putting in minimization here we need to include eofTarget
	 * into the minimization algorithm. It is currently set by the longest
	 * match operator and not considered anywhere else. */

	FsmAp *all;
	if ( numGraphs == 0 )
		all = FsmAp::lambdaFsm( fsmCtx );
	else {
		/* Add all the other graphs into the first. */
		all = graphs[0];
		all->globOp( graphs+1, numGraphs-1 );
	}
	delete[] graphs;

	/* Go through all the token regions and check for lmRequiresErrorState. */
	for ( RegionImplList::Iter reg = regionImplList; reg.lte(); reg++ ) {
		if ( reg->lmSwitchHandlesError )
			fsmCtx->lmRequiresErrorState = true;
	}

	return all;
}

/* This stands in for FsmCtx::analyzeGraph, which walks the context's own
 * action list. Colm keeps its actions in the compiler. */
void Compiler::analyzeGraph( FsmAp *graph )
{
	for ( ActionList::Iter act = actionList; act.lte(); act++ )
		fsmCtx->analyzeAction( act, act->inlineList );

	for ( StateList::Iter st = graph->stateList; st.lte(); st++ ) {
		/* The transition list. Colm never embeds conditions, so every
		 * transition is plain. */
		for ( TransList::Iter trans = st->outList; trans.lte(); trans++ ) {
			for ( ActionTable::Iter at = trans->tdap()->actionTable; at.lte(); at++ )
				at->value->numTransRefs += 1;
		}

		for ( ActionTable::Iter at = st->toStateActionTable; at.lte(); at++ )
			at->value->numToStateRefs += 1;

		for ( ActionTable::Iter at = st->fromStateActionTable; at.lte(); at++ )
			at->value->numFromStateRefs += 1;

		for ( ActionTable::Iter at = st->eofActionTable; at.lte(); at++ )
			at->value->numEofRefs += 1;
	}
}

FsmAp *Compiler::makeScanner()
{
	/* Make the graph, do minimization. */
	FsmAp *fsmGraph = makeAllRegions();

	/* If any errors have occured in the input file then don't write anything. */
	if ( gblErrorCount > 0 )
		return 0;

	analyzeGraph( fsmGraph );

	/* Add the error state if one is needed and number the states. */
	fsmCtx->prepareReduction( fsmGraph );

	return fsmGraph;
}

LangEl *Compiler::makeRepeatProd( const InputLoc &loc, Namespace *nspace,
		const String &repeatName, UniqueType *ut, bool left )
{
	LangEl *prodName = addLangEl( this, nspace, repeatName, LangEl::NonTerm );
	prodName->isRepeat = true;
	prodName->leftRecursive = left;

	ProdElList *prodElList1 = new ProdElList;

	/* Build the first production of the repeat. */
	TypeRef *typeRef1 = TypeRef::cons( loc, ut );
	ProdEl *factor1 = new ProdEl( ProdEl::ReferenceType,
			InputLoc(), 0, false, typeRef1, 0 );

	UniqueType *prodNameUT = findUniqueType( TYPE_TREE, prodName );
	TypeRef *typeRef2 = TypeRef::cons( loc, prodNameUT );
	ProdEl *factor2 = new ProdEl( ProdEl::ReferenceType,
			InputLoc(), 0, false, typeRef2, 0 );

	if ( left ) {
		prodElList1->append( factor2 );
		prodElList1->append( factor1 );
	}
	else {
		prodElList1->append( factor1 );
		prodElList1->append( factor2 );
	}

	Production *newDef1 = Production::cons( InputLoc(),
			prodName, prodElList1, String(), false, 0,
			prodList.length(), prodName->prodList.length() );

	prodName->prodList.append( newDef1 );
	prodList.append( newDef1 );

	/* Build the second production of the repeat. */
	ProdElList *prodElList2 = new ProdElList;

	Production *newDef2 = Production::cons( InputLoc(),
			prodName, prodElList2, String(), false, 0,
			prodList.length(), prodName->prodList.length() );

	prodName->prodList.append( newDef2 );
	prodList.append( newDef2 );

	return prodName;
}

LangEl *Compiler::makeListProd( const InputLoc &loc, Namespace *nspace,
		const String &listName, UniqueType *ut, bool left )
{
	LangEl *prodName = addLangEl( this, nspace, listName, LangEl::NonTerm );
	prodName->isList = true;
	prodName->leftRecursive = left;

	/* Build the first production of the list. */
	TypeRef *typeRef1 = TypeRef::cons( loc, ut );
	ProdEl *factor1 = new ProdEl( ProdEl::ReferenceType, InputLoc(), 0, false, typeRef1, 0 );

	UniqueType *prodNameUT = findUniqueType( TYPE_TREE, prodName );
	TypeRef *typeRef2 = TypeRef::cons( loc, prodNameUT );
	ProdEl *factor2 = new ProdEl( ProdEl::ReferenceType, loc, 0, false, typeRef2, 0 );

	ProdElList *prodElList1 = new ProdElList;
	if ( left ) {
		prodElList1->append( factor2 );
		prodElList1->append( factor1 );
	}
	else {
		prodElList1->append( factor1 );
		prodElList1->append( factor2 );
	}

	Production *newDef1 = Production::cons( loc,
			prodName, prodElList1, String(), false, 0,
			prodList.length(), prodName->prodList.length() );

	prodName->prodList.append( newDef1 );
	prodList.append( newDef1 );

	/* Build the second production of the list. */
	TypeRef *typeRef3 = TypeRef::cons( loc, ut );
	ProdEl *factor3 = new ProdEl( ProdEl::ReferenceType, loc, 0, false, typeRef3, 0 );

	ProdElList *prodElList2 = new ProdElList;
	prodElList2->append( factor3 );

	Production *newDef2 = Production::cons( loc,
			prodName, prodElList2, String(), false, 0,
			prodList.length(), prodName->prodList.length() );

	prodName->prodList.append( newDef2 );
	prodList.append( newDef2 );

	return prodName;
}

LangEl *Compiler::makeOptProd( const InputLoc &loc, Namespace *nspace,
		const String &optName, UniqueType *ut )
{
	LangEl *prodName = addLangEl( this, nspace, optName, LangEl::NonTerm );
	prodName->isOpt = true;

	ProdElList *prodElList1 = new ProdElList;

	/* Build the first production of the repeat. */
	TypeRef *typeRef1 = TypeRef::cons( loc, ut );
	ProdEl *factor1 = new ProdEl( ProdEl::ReferenceType, loc, 0, false, typeRef1, 0 );
	prodElList1->append( factor1 );

	Production *newDef1 = Production::cons( loc,
			prodName, prodElList1, String(), false, 0,
			prodList.length(), prodName->prodList.length() );

	prodName->prodList.append( newDef1 );
	prodList.append( newDef1 );

	/* Build the second production of the repeat. */
	ProdElList *prodElList2 = new ProdElList;

	Production *newDef2 = Production::cons( loc,
			prodName, prodElList2, String(), false, 0,
			prodList.length(), prodName->prodList.length() );

	prodName->prodList.append( newDef2 );
	prodList.append( newDef2 );

	return prodName;
}

Namespace *Namespace::findNamespace( const String &name )
{
	for ( NamespaceVect::Iter c = childNamespaces; c.lte(); c++ ) {
		if ( strcmp( name, (*c)->name ) == 0 )
			return *c;
	}
	return 0;
}

Reduction *Namespace::findReduction( const String &name )
{
	for ( ReductionVect::Iter r = reductions; r.lte(); r++ ) {
		if ( strcmp( name, (*r)->name ) == 0 )
			return *r;
	}
	return 0;
}

/* Search from a previously resolved qualification. (name 1+ in a qual list). */
Namespace *NamespaceQual::searchFrom( Namespace *from, StringVect::Iter &qualPart )
{
	/* While there are still parts in the qualification.  */
	while ( qualPart.lte() ) {
		Namespace *child = from->findNamespace( *qualPart );
		if ( child == 0 )
			return 0;

		from = child;
		qualPart.increment();
	}

	return from;
}

Namespace *NamespaceQual::getQual( Compiler *pd )
{
	/* Do the search only once. */
	if ( cachedNspaceQual != 0 )
		return cachedNspaceQual;

	if ( qualNames.length() == 0 ) {
		/* No qualification, use the region the qualification was
		 * declared in. */
		cachedNspaceQual = declInNspace;
	}
	else if ( strcmp( qualNames[0], "root" ) == 0 ) {
		/* First item is "root." Start the downward search from there. */
		StringVect::Iter qualPart = qualNames;
		qualPart.increment();
		cachedNspaceQual = searchFrom( pd->rootNamespace, qualPart );
		return cachedNspaceQual;
	}
	else {
		/* Have a qualification. Move upwards through the declared
		 * regions looking for the first part. */
		StringVect::Iter qualPart = qualNames;
		Namespace *parentNamespace = declInNspace;
		while ( parentNamespace != 0 ) {
			/* Search for the first part underneath the current parent. */
			Namespace *child = parentNamespace->findNamespace( *qualPart );

			if ( child != 0 ) {
				/* Found the first part. Start going below the result.  */
				qualPart.increment();
				cachedNspaceQual = searchFrom( child, qualPart );
				return cachedNspaceQual;
			}

			/* Not found, move up to the parent. */
			parentNamespace = parentNamespace->parentNamespace;
		}

		/* Failed to find the place to start from. */
		cachedNspaceQual = 0;
	}

	return cachedNspaceQual;
}

void Compiler::initEmptyScanner( RegionSet *regionSet, TokenRegion *reg )
{
	if ( reg != 0 && reg->impl->tokenInstanceList.length() == 0 ) {
		reg->impl->wasEmpty = true;

		static int def = 1;
		String name( 64, "__%d_DEF_PAT_%d", reg->id, def++ );

		LexJoin *join = LexJoin::cons( LexExpression::cons( BT_Any ) );

		TokenDef *tokenDef = TokenDef::cons( name, String(), false, false,
				join, 0, internal, rootNamespace, regionSet, 0, 0 );

		/* The definition no longer takes an id, but keep skipping one so
		 * the scanner's token ids are unchanged. */
		nextTokenId++;

		TokenInstance *tokenInstance = TokenInstance::cons( tokenDef,
				join, internal, nextTokenId++,
				rootNamespace, reg );

		reg->impl->addToken( tokenInstance );

		/* These do not go in the namespace so so they cannot get declared
		 * in the declare pass. */
		LangEl *lel = addLangEl( this, rootNamespace, name, LangEl::Term );

		tokenInstance->tokenDef->tdLangEl = lel;
		lel->tokenDef = tokenDef;
	}
}

void Compiler::initEmptyScanners()
{
	for ( RegionSetList::Iter regionSet = regionSetList; regionSet.lte(); regionSet++ ) {
		initEmptyScanner( regionSet, regionSet->tokenIgnore );
		initEmptyScanner( regionSet, regionSet->tokenOnly );
		initEmptyScanner( regionSet, regionSet->ignoreOnly );
		initEmptyScanner( regionSet, regionSet->collectIgnore );
	}
}

pda_run *Compiler::parsePattern( program_t *prg, tree_t **sp, const InputLoc &loc,
		int parserId, struct input_impl *sourceStream )
{
	struct pda_run *pdaRun = new pda_run;
	colm_pda_init( prg, pdaRun, pdaTables, parserId, 0, false, 0, false );

	long pcr = colm_parse_loop( prg, sp, pdaRun, sourceStream, PCR_START );
	assert( pcr == PCR_DONE );
	if ( pdaRun->parse_error ) {
		cerr << locFileName( loc ) << ":" << loc.line << ":" << loc.col;

		if ( pdaRun->parse_error_text != 0 ) {
			colm_data *tokdata = pdaRun->parse_error_text->tokdata;
			cerr << ": relative error: ";
			cerr.write( (const char*)tokdata->data, tokdata->length );
		}
		else {
			cerr << ": parse error";
		}

		cerr << endl;
		gblErrorCount += 1;
	}

	return pdaRun;
}

void Compiler::parsePatterns()
{
	program_t *prg = colm_new_program( runtimeData );

	colm_set_debug( prg, gblActiveRealm );

	/* Turn off context-dependent parsing. */
	prg->ctx_dep_parsing = 0;
	prg->dump_lexer = dumpLexer;

	tree_t **sp = prg->stack_root;

	for ( ConsList::Iter cons = replList; cons.lte(); cons++ ) {
		if ( cons->langEl != 0 ) {
			struct input_impl *in = colm_impl_new_cons( strdup("<internal>"), cons );
			cons->pdaRun = parsePattern( prg, sp, cons->loc, cons->langEl->parserId, in );
		}
	}

	for ( PatList::Iter pat = patternList; pat.lte(); pat++ ) {
		struct input_impl *in = colm_impl_new_pat( strdup("<internal>"), pat );
		pat->pdaRun = parsePattern( prg, sp, pat->loc, pat->langEl->parserId, in );
	}

	/* Bail on above errors. */
	if ( gblErrorCount > 0 )
		exit(1);

	fillInPatterns( prg );
}

void Compiler::collectParserEls( BstSet<LangEl*> &parserEls )
{
	for ( PatList::Iter pat = patternList; pat.lte(); pat++ ) {
		/* We assume the reduction action compilation phase was run before
		 * pattern parsing and it decorated the pattern with the target type. */
		assert( pat->langEl != 0 );
		if ( pat->langEl->type != LangEl::NonTerm )
			error(pat->loc) << "pattern type is not a non-terminal" << endp;

		if ( pat->langEl->parserId < 0 ) {
			/* Make a parser for the language element. */
			parserEls.insert( pat->langEl );
			pat->langEl->parserId = nextParserId++;
		}
	}

	for ( ConsList::Iter repl = replList; repl.lte(); repl++ ) {
		/* We need the the language element from the compilation process. */
		assert( repl->langEl != 0 );

		if ( repl->langEl->parserId < 0 ) {
			/* Make a parser for the language element. */
			parserEls.insert( repl->langEl );
			repl->langEl->parserId = nextParserId++;
		}
	}

	/* Make parsers that we need. */
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		if ( lel->parserId >= 0 )
			parserEls.insert( lel );
	}
}

/* Two alternatives are the same production if their right-hand sides are the
 * same sequence of language elements. Capture fields and reduction actions
 * are deliberately ignored: an identical RHS is a duplicate whichever action
 * is attached. */
static bool sameProductionRhs( Production *a, Production *b )
{
	ProdEl *ea = a->prodElList != 0 ? a->prodElList->head : 0;
	ProdEl *eb = b->prodElList != 0 ? b->prodElList->head : 0;
	while ( ea != 0 && eb != 0 ) {
		if ( ea->langEl != eb->langEl )
			return false;
		ea = ea->next;
		eb = eb->next;
	}
	return ea == 0 && eb == 0;
}

/* If a production is a unit production `A -> B` (exactly one symbol on the
 * right-hand side and it is a non-terminal), return B; otherwise 0. */
static LangEl *unitProductionTarget( Production *prod )
{
	if ( prod->prodElList == 0 )
		return 0;
	ProdEl *el = prod->prodElList->head;
	if ( el == 0 || el->next != 0 )
		return 0;
	LangEl *to = el->langEl;
	if ( to == 0 || to->type != LangEl::NonTerm )
		return 0;
	return to;
}

/*
 * Static grammar diagnostics: unreachable non-terminals, unproductive
 * (non-deriving) non-terminals, and duplicate productions. These are purely
 * structural checks over the resolved grammar, independent of the PDA, and run
 * on every compile. They only ever write to stderr; generated code is
 * unaffected.
 *
 * This is deliberately NOT a guarantee that a reduction can never win at
 * runtime. That question depends on the PDA's action order and the retry loop
 * and is input-dependent; see GRAMMAR_DIAGNOSTICS_TASK.md section 3.2.
 */
void Compiler::reportGrammarDiagnostics( LangElSet &parserEls )
{
	if ( gblErrorCount > 0 )
		return;

	/* --no-warn-grammar disables the whole pass. */
	if ( !warnGrammar )
		return;

	/* The PDA report owns the report stream (stderr by default); keep the
	 * machine-readable JSON pure and the text report free of interleaving. */
	if ( pdaReportMode != PdaReportOff )
		return;

	/* Reachability: BFS from the parse roots through production right-hand
	 * sides. */
	LangElVect queue;
	LangElSet reachable;
	long nRoots = 0;
	for ( LangElSet::Iter pe = parserEls; pe.lte(); pe++ ) {
		nRoots++;
		if ( reachable.insert( *pe ) != 0 )
			queue.append( *pe );
	}

	/* A translation unit with no parse roots of its own is a library-style
	 * include (for example src/colm/colm.lm). Every non-terminal would look
	 * unreachable, which is not actionable, so leave that check off. */
	bool reportUnreachable = nRoots > 0;

	for ( long qi = 0; qi < queue.length(); qi++ ) {
		LangEl *lel = queue[qi];
		for ( LelProdList::Iter prod = lel->prodList; prod.lte(); prod++ ) {
			if ( prod->prodElList == 0 )
				continue;
			for ( ProdElList::Iter el = *prod->prodElList; el.lte(); el++ ) {
				LangEl *to = el->langEl;
				if ( to != 0 && to->type == LangEl::NonTerm &&
						reachable.insert( to ) != 0 )
					queue.append( to );
			}
		}
	}

	/* Productivity: a non-terminal is productive if it has some production
	 * whose right-hand side is all terminals or already-productive
	 * non-terminals. Iterate to a fixed point. */
	LangElSet productive;
	bool changed = true;
	while ( changed ) {
		changed = false;
		for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
			if ( lel->type != LangEl::NonTerm || productive.find( lel ) != 0 )
				continue;
			for ( LelProdList::Iter prod = lel->prodList; prod.lte(); prod++ ) {
				bool ok = true;
				if ( prod->prodElList != 0 ) {
					for ( ProdElList::Iter el = *prod->prodElList; el.lte(); el++ ) {
						LangEl *to = el->langEl;
						if ( to != 0 && to->type == LangEl::NonTerm &&
								productive.find( to ) == 0 ) {
							ok = false;
							break;
						}
					}
				}
				if ( ok ) {
					productive.insert( lel );
					changed = true;
					break;
				}
			}
		}
	}

	/* Nullability: a non-terminal is nullable if some production has an empty
	 * right-hand side or one whose symbols are all already-nullable
	 * non-terminals. Iterate to a fixed point. Used by the EBNF check below. */
	LangElSet nullable;
	changed = true;
	while ( changed ) {
		changed = false;
		for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
			if ( lel->type != LangEl::NonTerm || nullable.find( lel ) != 0 )
				continue;
			for ( LelProdList::Iter prod = lel->prodList; prod.lte(); prod++ ) {
				bool ok = true;
				if ( prod->prodElList != 0 ) {
					for ( ProdElList::Iter el = *prod->prodElList; el.lte(); el++ ) {
						LangEl *to = el->langEl;
						if ( to == 0 )
							continue;
						if ( to->type != LangEl::NonTerm ||
								nullable.find( to ) == 0 ) {
							ok = false;
							break;
						}
					}
				}
				if ( ok ) {
					nullable.insert( lel );
					changed = true;
					break;
				}
			}
		}
	}

	int nUnreachable = 0, nUnproductive = 0, nDuplicate = 0, nSubsumed = 0;
	int nRedundantEbnf = 0;

	/* Unit closure: for each non-terminal, the set of non-terminals reachable
	 * from it through unit productions `A -> B`. Used to detect alternatives
	 * like `X -> B` that are already covered by `X -> C` when B is reachable
	 * from C. Computed once for the whole grammar. */
	BstMap<LangEl*, LangElSet*> unitClosure;
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		if ( lel->type != LangEl::NonTerm )
			continue;
		LangElSet *cl = new LangElSet;
		LangElVect stack;
		BstSet<LangEl*> seen;
		stack.append( lel );
		seen.insert( lel );
		for ( long si = 0; si < stack.length(); si++ ) {
			LangEl *cur = stack[si];
			for ( LelProdList::Iter p = cur->prodList; p.lte(); p++ ) {
				LangEl *to = unitProductionTarget( p );
				if ( to != 0 && seen.insert( to ) != 0 ) {
					cl->insert( to );
					stack.append( to );
				}
			}
		}
		unitClosure.insert( lel, cl );
	}

	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		if ( lel->type != LangEl::NonTerm )
			continue;
		if ( lel == noTokenLangEl || lel == eofLangEl || lel == errorLangEl ||
				lel == anyLangEl || lel == rootLangEl )
			continue;
		/* EBNF sugar elements are reported through their parent. */
		if ( lel->isRepeat || lel->isList || lel->isOpt )
			continue;

		bool isReachable = reachable.find( lel ) != 0;
		bool isProductive = productive.find( lel ) != 0;

		Production *first = lel->prodList.head;

		if ( !isReachable ) {
			if ( !reportUnreachable )
				continue;
			if ( inputFn != 0 ) {
				if ( first != 0 && first->loc.line >= 0 )
					warning( first->loc ) << "non-terminal '" << lel->name
							<< "' is unreachable (not used by any parse rule)" << endl;
				else
					warning() << "non-terminal '" << lel->name
							<< "' is unreachable (not used by any parse rule)" << endl;
			}
			nUnreachable++;
			continue;
		}

		if ( !isProductive ) {
			if ( inputFn != 0 ) {
				if ( first != 0 && first->loc.line >= 0 )
					warning( first->loc ) << "non-terminal '" << lel->name
							<< "' cannot derive any terminal string" << endl;
				else
					warning() << "non-terminal '" << lel->name
							<< "' cannot derive any terminal string" << endl;
			}
			nUnproductive++;
			continue;
		}

		/* Duplicate alternatives: identical right-hand sides. */
		Vector<Production*> alts;
		for ( LelProdList::Iter p = lel->prodList; p.lte(); p++ )
			alts.append( p );
		for ( long ai = 0; ai < alts.length(); ai++ ) {
			for ( long aj = ai + 1; aj < alts.length(); aj++ ) {
				if ( sameProductionRhs( alts[ai], alts[aj] ) ) {
					Production *p1 = alts[ai], *p2 = alts[aj];
					if ( inputFn != 0 )
						warning( p2->loc ) << "duplicate production for '" << lel->name
								<< "' (same as the rule at " << p1->loc.fileName << ":"
								<< p1->loc.line << ")" << endl;
					nDuplicate++;
				}
			}
		}

		/* Unit-subsumed alternatives. If `X -> B` and `X -> C` are both unit
		 * productions and B is reachable from C through unit productions, then
		 * the `X -> B` alternative is already covered by `X -> C`. */
		for ( long ai = 0; ai < alts.length(); ai++ ) {
			LangEl *b = unitProductionTarget( alts[ai] );
			if ( b == 0 )
				continue;
			for ( long aj = 0; aj < alts.length(); aj++ ) {
				if ( aj == ai )
					continue;
				LangEl *c = unitProductionTarget( alts[aj] );
				if ( c == 0 || c == b )
					continue;
				BstMapEl<LangEl*, LangElSet*> *cEl = unitClosure.find( c );
				if ( cEl == 0 || cEl->value->find( b ) == 0 )
					continue;
				/* Mutual reachability is a unit cycle, not a subsumption. */
				BstMapEl<LangEl*, LangElSet*> *bEl = unitClosure.find( b );
				if ( bEl != 0 && bEl->value->find( c ) != 0 )
					continue;
				if ( inputFn != 0 )
					warning( alts[ai]->loc ) << "alternative '" << lel->name
							<< " -> " << b->name << "' is subsumed by '" << lel->name
							<< " -> " << c->name << "' (" << b->name
							<< " is reachable from " << c->name
							<< " through unit productions)" << endl;
				nSubsumed++;
				break;
			}
		}
	}

	/* EBNF sugar applied to an already-nullable operand. `X?` is exactly `X`
	 * when X is nullable, and `X*`/`X+` can derive the empty string in
	 * unboundedly many ways; all are ambiguous and usually a mistake. The
	 * generated element records its operand in `repeatOf`; report at the
	 * sugar site when the generated production carries a location (the opt and
	 * list builders do), otherwise at the operand's own definition. */
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		if ( !(lel->isRepeat || lel->isList || lel->isOpt) )
			continue;
		if ( reachable.find( lel ) == 0 )
			continue;
		LangEl *op = lel->repeatOf;
		if ( op == 0 || op->type != LangEl::NonTerm )
			continue;
		if ( nullable.find( op ) == 0 )
			continue;

		const char *opname = lel->isOpt ? "?" : ( lel->isList ? "+" : "*" );
		Production *ebnfFirst = lel->prodList.head;
		Production *opFirst = op->prodList.head;
		bool haveLoc = ebnfFirst != 0 && ebnfFirst->loc.line >= 0;
		if ( inputFn != 0 && ( haveLoc || ( opFirst != 0 && opFirst->loc.line >= 0 ) ) ) {
			const InputLoc &loc = haveLoc ? ebnfFirst->loc : opFirst->loc;
			warning( loc ) << "EBNF '" << opname << "' on nullable '"
					<< op->name << "' has no effect ('" << op->name
					<< "' can already derive the empty string)" << endl;
		}
		else
			warning() << "EBNF '" << opname << "' on nullable '" << op->name
					<< "' has no effect" << endl;
		nRedundantEbnf++;
	}

	if ( nUnreachable != 0 || nUnproductive != 0 || nDuplicate != 0 ||
			nSubsumed != 0 || nRedundantEbnf != 0 ) {
		cerr << "grammar: " << nUnreachable << " unreachable, "
				<< nUnproductive << " unproductive, "
				<< nDuplicate << " duplicate, "
				<< nSubsumed << " subsumed, "
				<< nRedundantEbnf << " ebnf-redundant" << endl;
	}
}

void Compiler::writeHostCall()
{
	/*
	 * Host Call
	 */
	for ( FunctionList::Iter hc = inHostList; hc.lte(); hc++ ) {
		*outStream <<
			"value_t " << hc->hostCall << "( program_t *prg, tree_t **sp";
		for ( ParameterList::Iter p = *hc->paramList; p.lte(); p++ ) {
			*outStream <<
				", value_t";
		}
		*outStream << " );\n";
	}

	*outStream <<
		"tree_t **" << objectName << "_host_call( program_t *prg, long code, tree_t **sp )\n"
		"{\n"
		"	value_t rtn = 0;\n"
		"	switch ( code ) {\n";

	for ( FunctionList::Iter hc = inHostList; hc.lte(); hc++ ) {
		*outStream <<
			"		case " << hc->funcId << ": {\n";

		int pos = hc->paramList->length() - 1;
		for ( ParameterList::Iter p = *hc->paramList; p.lte(); p++, pos-- ) {
			*outStream <<
				"			value_t p" << pos << " = vm_pop_value();\n";
		}

		*outStream <<
			"			rtn = " << hc->hostCall << "( prg, sp";

		pos = 0;
		for ( ParameterList::Iter p = *hc->paramList; p.lte(); p++, pos++ ) {
			*outStream <<
				", p" << pos;
		}
		*outStream << " );\n"
			"			break;\n"
			"		}\n";
	}

	*outStream <<
		"	}\n"
		"	vm_push_value( rtn );\n"
		"	return sp;\n"
		"}\n";

}

void Compiler::generateOutput( long activeRealm, bool includeCommit )
{
	FsmCodeGen *fsmGen = new FsmCodeGen( reducer, *outStream, fsmTables );
	fsmGen->genAnalysis();

	PdaCodeGen *pdaGen = new PdaCodeGen( *outStream );

	fsmGen->writeIncludes();
	pdaGen->defineRuntime();
	fsmGen->writeCode();

	/* Make parsers that we need. */
	pdaGen->writeParserData( 0, pdaTables );

	/* Write the runtime data. */
	pdaGen->writeRuntimeData( runtimeData, pdaTables );

	writeHostCall();

	if ( includeCommit )
		writeCommitStub();

	if ( !gblLibrary )
		fsmGen->writeMain( activeRealm );

	outStream->flush();

	if ( outLexSmStream ) {
		fsmGen->writeDebugFsm(*outLexSmStream);
		outLexSmStream->flush();
	}
}

/* Write the reduced lexer FSM without generating any code. Used by
 * --dump-lexer-sm together with --syntax-only, where generateOutput (and with
 * it the only other call to writeDebugFsm) is skipped. The reducer and the
 * scanner tables are already built by compile(), so the reduced FSM is
 * available. Generated code is written to a sink and discarded. */
void Compiler::dumpLexerSm()
{
	ostringstream sink;
	FsmCodeGen *fsmGen = new FsmCodeGen( reducer, sink, fsmTables );
	fsmGen->genAnalysis();
	fsmGen->writeDebugFsm( *outLexSmStream );
	outLexSmStream->flush();
	delete fsmGen;
}


void Compiler::prepGrammar()
{
	/* This will create language elements. */
	wrapNonTerminals();

	makeLangElIds();
	makeStructElIds();
	makeLangElNames();
	makeDefinitionNames();
	noUndefindLangEls();

	/* Put the language elements in an index by language element id. */
	langElIndex = new LangEl*[nextLelId+1];
	memset( langElIndex, 0, sizeof(LangEl*)*(nextLelId+1) );
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ )
		langElIndex[lel->id] = lel;

	makeProdFsms();

	/* Allocate the Runtime data now. Every PdaTable that we make
	 * will reference it, but it will be filled in after all the tables are
	 * built. */
	runtimeData = new colm_sections;
}

void Compiler::compile()
{
	initKeyOps();

	/* Declare types. */
	declarePass();

	/* Resolve type references. */
	resolvePass();

	makeTerminalWrappers();
	makeEofElements();

	/*
	 * Parsers
	 */

	/* Init the longest match data */
	initLongestMatchData();
	FsmAp *fsmGraph = makeScanner();

	/* Lexer errors leave us with no scanner graph. Bail on them. */
	if ( gblErrorCount > 0 )
		exit(1);

	prepGrammar();

	placeAllLanguageObjects();
	placeAllStructObjects();
	placeAllFrameObjects();
	placeAllFunctions();

	/* Compile bytecode. */
	compileByteCode();

	/* Make the reduced scanner. */
	reducer = new LexReducer( this, fsmGraph );
	reducer->reduce();

	BstSet<LangEl*> parserEls;
	collectParserEls( parserEls );

	reportGrammarDiagnostics( parserEls );

	makeParser( parserEls );

	/* Make the scanner tables. */
	fsmTables = reducer->makeFsmTables();

	/* Now that all parsers are built, make the global runtimeData. */
	makeRuntimeData();

	/*
	 * All compilation is now complete.
	 */

	/* Parse constructors and patterns. */
	parsePatterns();
}

int Compiler::execute()
{
    compile();

    if ( gblErrorCount > 0 )
        return 1;

    return executeScanner();
}

int Compiler::executeScanner()
{
    return 0;
}

void Compiler::dumpRepeatType( const RepeatType repeatType )
{
	switch ( repeatType ) {
		case RepeatNone:
			break;

		case RepeatRepeat:
			cerr << " repeat";
			break;

		case RepeatList:
			cerr << " list";
			break;

		case RepeatOpt:
			cerr << " optional";
			break;

		case RepeatLeftRepeat:
			cerr << " left-repeat";
			break;

		case RepeatLeftList:
			cerr << " left-list";
			break;

		default:
			cerr << " <repeat>";
			break;
	}
}

void Compiler::dumpNamespaceQual( const NamespaceQual *nspaceQual )
{
	if ( nspaceQual == 0 )
		return;

	for ( StringVect::Iter it = nspaceQual->qualNames;
			it.lte(); it++ ) {
		cerr << *it << "::";
	}
}

void Compiler::dumpIterType( const IterDef *iterDef )
{
	if ( iterDef == 0 ) {
		cerr << "iter";
		return;
	}

	switch ( iterDef->type ) {
		case IterDef::Tree:
			cerr << "iter_tree";
			break;

		case IterDef::Child:
			cerr << "iter_child";
			break;

		case IterDef::RevChild:
			cerr << "iter_revchild";
			break;

		case IterDef::Repeat:
			cerr << "iter_repeat";
			break;

		case IterDef::RevRepeat:
			cerr << "iter_revrepeat";
			break;

		case IterDef::User:
			cerr << "iter_user";
			if ( iterDef->func != 0 ) {
				cerr << "(" << iterDef->func->name << ")";
			}
			break;

		case IterDef::ListEl:
			cerr << "iter_list_el";
			break;

		case IterDef::RevListVal:
			cerr << "iter_rev_list_val";
			break;

		case IterDef::MapEl:
			cerr << "iter_map_el";
			break;

		case IterDef::WithIgnore:
			cerr << "iter_with_ignore";
			break;

		default:
			cerr << "iter";
			break;
	}
}

void Compiler::dumpGenericType( const GenericType *generic )
{
	if ( generic == 0 ) {
		cerr << "generic";
		return;
	}

	/*
	 * GenericType itself is the runtime declaration. The resolved
	 * semantic type is represented by its element/key/value UniqueTypes.
	 */
	if ( generic->keyUt != 0 ) {
		cerr << "map<";
		dumpType( generic->keyUt );
		cerr << ", ";
		dumpType( generic->valueUt );
		cerr << ">";
	}
	else if ( generic->elUt != 0 ) {
		cerr << "list<";
		dumpType( generic->elUt );
		cerr << ">";
	}
	else {
		cerr << "generic";
	}
}

void Compiler::dumpType( const UniqueType *ut )
{
	if ( ut == 0 ) {
		cerr << "?";
		return;
	}

	switch ( ut->typeId ) {
		case TYPE_NOTYPE:
			cerr << "notype";
			break;

		case TYPE_NIL:
			cerr << "nil";
			break;

		case TYPE_TREE:
			if ( ut->langEl != 0 )
				cerr << ut->langEl->name;
			else
				cerr << "tree";
			break;

		case TYPE_REF:
			cerr << "ref";
			break;

		case TYPE_ITER:
			dumpIterType( ut->iterDef );
			break;

		case TYPE_STRUCT:
			if ( ut->structEl != 0 )
				cerr << ut->structEl->name;
			else
				cerr << "struct";
			break;

		case TYPE_GENERIC:
			dumpGenericType( ut->generic );
			break;

		case TYPE_INT:
			cerr << "int";
			break;

		case TYPE_BOOL:
			cerr << "bool";
			break;

		case TYPE_LIST_PTRS:
			cerr << "list_ptrs";
			break;

		case TYPE_MAP_PTRS:
			cerr << "map_ptrs";
			break;

		case TYPE_VOID:
			cerr << "void";
			break;

		default:
			cerr << "<unknown-type:"
				<< (int)ut->typeId << ">";
			break;
	}
}

void Compiler::dumpUniqueType( const UniqueType *ut )
{
	if ( ut == 0 ) {
		cerr << "?";
		return;
	}

	switch ( ut->typeId ) {
		case TYPE_NOTYPE:
			cerr << "<notype>";
			break;

		case TYPE_NIL:
			cerr << "nil";
			break;

		case TYPE_TREE:
			if ( ut->langEl != 0 )
				cerr << ut->langEl->name;
			else
				cerr << "tree";
			break;

		case TYPE_REF:
			cerr << "ref";
			break;

		case TYPE_ITER:
			cerr << "iter";
			break;

		case TYPE_STRUCT:
			cerr << "struct";

			if ( ut->structEl != 0 ) {
				cerr << " " << ut->structEl->name;
			}
			break;

		case TYPE_GENERIC:
			cerr << "generic";

			if ( ut->generic != 0 ) {
				cerr << " ";
				dumpGeneric( *ut->generic );
			}
			break;

		case TYPE_INT:
			cerr << "int";
			break;

		case TYPE_BOOL:
			cerr << "bool";
			break;

		case TYPE_LIST_PTRS:
			cerr << "list_ptrs";
			break;

		case TYPE_MAP_PTRS:
			cerr << "map_ptrs";
			break;

		case TYPE_VOID:
			cerr << "void";
			break;

		default:
			cerr << "<unknown-type:" << ut->typeId << ">";
			break;
	}
}

void Compiler::dumpTypeRef( const TypeRef *tr )
{
	if ( tr == 0 ) {
		cerr << "?";
		return;
	}

	if ( tr->uniqueType != 0 ) {
		dumpType( tr->uniqueType );
		return;
	}

	/*
	 * The compiler normally resolves TypeRefs before we get here.
	 * Keep a structural fallback so dumpGlobals remains useful if
	 * a declaration has not been resolved.
	 */
	switch ( tr->type ) {
		case TypeRef::Unspecified:
			cerr << "?";
			break;

		case TypeRef::Name:
			dumpNamespaceQual( tr->nspaceQual );
			cerr << tr->typeName;
			dumpRepeatType( tr->repeatType );
			break;

		case TypeRef::Literal:
			cerr << "<literal>";
			break;

		case TypeRef::Iterator:
			if ( tr->iterDef != 0 )
				dumpIterType( tr->iterDef );
			else
				cerr << "iter";
			break;

		case TypeRef::List:
			cerr << "list<";
			dumpTypeRef( tr->typeRef1 );
			cerr << ">";
			break;

		case TypeRef::ListPtrs:
			cerr << "list_ptrs<";
			dumpTypeRef( tr->typeRef1 );
			cerr << ">";
			break;

		case TypeRef::ListEl:
			cerr << "list_el<";
			dumpTypeRef( tr->typeRef1 );
			cerr << ">";
			break;

		case TypeRef::Map:
			cerr << "map<";
			dumpTypeRef( tr->typeRef1 );
			cerr << ", ";
			dumpTypeRef( tr->typeRef2 );
			cerr << ">";
			break;

		case TypeRef::MapEl:
			cerr << "map_el<";
			dumpTypeRef( tr->typeRef1 );
			cerr << ", ";
			dumpTypeRef( tr->typeRef2 );
			cerr << ">";
			break;

		case TypeRef::MapPtrs:
			cerr << "map_ptrs<";
			dumpTypeRef( tr->typeRef1 );
			cerr << ", ";
			dumpTypeRef( tr->typeRef2 );
			cerr << ">";
			break;

		case TypeRef::Parser:
			cerr << "parser<";
			dumpTypeRef( tr->typeRef1 );
			cerr << ">";
			break;

		case TypeRef::Ref:
			cerr << "&";
			dumpTypeRef( tr->typeRef1 );
			break;

		default:
			cerr << "<unknown-type-ref>";
			break;
	}
}

void Compiler::dumpField( const ObjectField *field )
{
	cerr << field->name;

	if ( field->typeRef != 0 ) {
		cerr << ": ";
		dumpTypeRef( field->typeRef );
	}

	if ( field->isConst )
		cerr << " const";
}

void Compiler::dumpMethod( const ObjectMethod *method )
{
	cerr << method->name << "(";

	if ( method->paramList != 0 ) {
		ParameterList::Iter param = *method->paramList;

		for ( long i = 0; i < method->numParams; i++, param++ ) {
			if ( i != 0 )
				cerr << ", ";

			cerr << param->name;

			cerr << ": ";

			if ( method->paramUTs != 0 )
				dumpType( method->paramUTs[i] );
			else
				dumpTypeRef( param->typeRef );

			if ( param->type == ObjectField::ParamRefType )
				cerr << " ref";
		}
	} else if ( method->paramUTs ) {
		for ( long i = 0; i < method->numParams; ++i) {
			if ( i != 0 )
				cerr << ", ";
			cerr << ": ";
			dumpUniqueType(method->paramUTs[i]);
		}

	}

	cerr << ")";

	if ( method->returnUT != 0 ) {
		cerr << ": ";
		dumpType( method->returnUT );
	}
	else if ( method->returnTypeRef != 0 ) {
		cerr << ": ";
		dumpTypeRef( method->returnTypeRef );
	}

	if ( method->isConst )
		cerr << " const";
}

void Compiler::dumpStruct( const StructDef &structDef )
{
	cerr << structDef.name;

	if ( structDef.objectDef == 0 ) {
		cerr << "\n";
		return;
	}

	cerr << " {\n";

	for ( FieldList::Iter it = structDef.objectDef->fieldList;
			it.lte(); it++ ) {
		cerr << "        ";
		dumpField( it->value );
		cerr << "\n";
	}

	cerr << "      }\n";
}

void Compiler::dumpTypeAlias( const TypeAlias &alias )
{
	cerr << alias.name << " = ";

	if ( alias.typeRef != 0 )
		dumpTypeRef( alias.typeRef );
	else
		cerr << "?";
}

void Compiler::dumpGeneric( const GenericType &generic )
{
	if ( generic.keyTr != 0 ) {
		cerr << "map<";
		dumpTypeRef( generic.keyTr );
		cerr << ", ";
		dumpTypeRef( generic.valueTr );
		cerr << ">";
	}
	else if ( generic.elTr != 0 ) {
		cerr << "list<";
		dumpTypeRef( generic.elTr );
		cerr << ">";
	}
	else {
		cerr << "?";
	}

	cerr << " [" << generic.typeId << "]";
}

void Compiler::dumpGlobals()
{
	cerr << "Global namespaces:\n";

	for ( NamespaceList::Iter ns = namespaceList; ns.lte(); ns++ ) {
		cerr << "  " << ns->name << "\n";

		cerr << "    fields:\n";
		for ( FieldMap::Iter it = ns->rootScope->fieldMap;
				it.lte(); it++ ) {
			cerr << "      ";
			dumpField( it->value );
			cerr << "\n";
		}

		cerr << "    methods:\n";
		for ( MethodMap::Iter it = ns->rootScope->methodMap;
				it.lte(); it++ ) {
			cerr << "      ";
			dumpMethod( it->value );
			cerr << "\n";
		}

		cerr << "    structs:\n";
		for ( StructDefList::Iter it = ns->structDefList;
				it.lte(); it++ ) {
			cerr << "      ";
			dumpStruct( *it );
		}

		cerr << "    generics:\n";
		for ( GenericList::Iter it = ns->genericList;
				it.lte(); it++ ) {
			cerr << "      ";

			if ( it->keyUt != 0 ) {
				cerr << "map<";
				dumpType( it->keyUt );
				cerr << ", ";
				dumpType( it->valueUt );
				cerr << ">";
			}
			else if ( it->elUt != 0 ) {
				cerr << "list<";
				dumpType( it->elUt );
				cerr << ">";
			}
			else {
				cerr << "generic";
			}

			cerr << "\n";
		}

		cerr << "    aliases:\n";
		for ( TypeAliasList::Iter it = ns->typeAliasList;
				it.lte(); it++ ) {
			cerr << "      ";
			dumpTypeAlias( *it );
			cerr << "\n";
		}

		cerr << "    rl definitions:\n";
		for ( GraphDict::Iter it = ns->rlMap;
				it.lte(); it++ ) {
			cerr << "      " << it->key;
			if ( it->loc.fileName != 0 && it->loc.fileName[0] != 0 ) {
				cerr << "  (" << it->loc.fileName << ":"
					<< it->loc.line << ":" << it->loc.col << ")";
			}
			cerr << "\n";
		}
	}

	cerr << "Global regions:\n";

	for ( RegionList::Iter it = regionList; it.lte(); it++ ) {
		cerr << "  " << it->id << ":"
			<< it->loc.fileName << ":"
			<< it->loc.line << ":"
			<< it->loc.col << "\n";
	}

	cerr << "Global region implementations: "
		<< regionImplList.length() << "\n";

	cerr << "Global region sets:\n";

	for ( RegionSetList::Iter it = regionSetList; it.lte(); it++ ) {
		cerr << "  " << it->loc.fileName << ":"
			<< it->loc.line << ":"
			<< it->loc.col << "\n";
	}
}

void Compiler::dumpRegions()
{
	cerr << "regions: " << regionList.length() << "\n";

	for ( RegionList::Iter reg = regionList; reg.lte(); reg++ ) {
		cerr << "  " << reg->id << ": "
			<< reg->loc.fileName << ":"
			<< reg->loc.line << ":"
			<< reg->loc.col;

		if ( reg->impl->defaultTokenInstance != 0 ) {
			cerr << " default="
				<< reg->impl->defaultTokenInstance->tokenDef->name;
		}

		cerr << "\n    tokens:";

		for ( TokenInstanceListReg::Iter t = reg->impl->tokenInstanceList;
				t.lte(); t++ ) {
			cerr << " " << t->tokenDef->name;
		}

		cerr << "\n";
	}
}
