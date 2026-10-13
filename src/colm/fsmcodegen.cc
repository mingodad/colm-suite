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
#include <string.h>
#include <stdbool.h>

#include <sstream>
#include <iostream>

#include "fsmcodegen.h"

using std::ostream;
using std::ostringstream;
using std::string;
using std::cerr;
using std::endl;

LexReducer::LexReducer( Compiler *pd, FsmAp *fsm )
:
	Reducer( pd->fsmGbl, pd->fsmCtx, fsm, "parser", 0 ),
	pd(pd),
	lexActions(0)
{
}

LexReducer::~LexReducer()
{
	delete[] lexActions;
}

void LexReducer::reduce()
{
	/* Both or neither, which eofTrans depends on. */
	for ( StateList::Iter st = fsm->stateList; st.lte(); st++ )
		assert( !( (st->eofTarget != 0) xor (st->eofActionTable.length() > 0) ) );

	make();

	/* Every action in the scanner graph is a LexAction. */
	lexActions = new LexAction*[actionList.length()];
	for ( ActionList::Iter act = fsmCtx->actionList; act.lte(); act++ ) {
		if ( act->actionId >= 0 )
			lexActions[act->actionId] = LexAction::cast( act );
	}

	/* Order the states for the code generator, depth first from the start
	 * state. The ordering walks the ranges before the singles and default
	 * are taken out of them. */
	redFsm->depthFirstOrdering();

	/* The table driven scanner that runs at compile time reads the singles,
	 * ranges and default of each state. Choose them here, where the tables
	 * are made from the machine, not in the code generator. */
	redFsm->chooseDefaultSpan();
	redFsm->moveSelectTransToSingle();

	redFsm->setInTrans();

	analyzeMachine();
}

/* Colm writes its own keys and needs no line directives, so the code
 * generator gets neither an alphabet type nor a line directive writer. */
FsmCodeGen::FsmCodeGen( LexReducer *reducer, ostream &out, fsm_tables *fsmTables )
:
	CodeGen( CodeGenArgs( reducer->id, reducer, 0, 0, "", "parser",
			out, GenIpGoto, 0, Direct ) ),
	reducer(reducer),
	fsmTables(fsmTables),
	skipTokprefLabelNeeded(false)
{
}

string FsmCodeGen::GET_KEY()
{
	ostringstream ret;
	/* Expression for retrieving the key, use simple dereference. */
	ret << "(*" << P() << ")";
	return ret.str();
}

/* Write out level number of tabs. Makes the nested binary search nice
 * looking. */
string FsmCodeGen::TABS( int level )
{
	string result;
	while ( level-- > 0 )
		result += "\t";
	return result;
}

/* Write out a key from the fsm code gen. Depends on wether or not the key is
 * signed. */
string FsmCodeGen::KEY( Key key )
{
	ostringstream ret;
	ret << key.getVal();
	return ret.str();
}

void FsmCodeGen::SET_ACT( ostream &ret, InlineItem *item )
{
	ret << ACT() << " = " << item->longestMatchPart->longestMatchId << ";";
}

void FsmCodeGen::SET_TOKEND( ostream &ret, InlineItem *item )
{
	/* The tokend action sets tokend. */
	ret << "{ " << TOKEND() << " = " << TOKPREF() << " + ( " << P() << " - " << BLOCK_START() << " ) + 1; }";
}

void FsmCodeGen::SET_TOKEND_0( ostream &ret, InlineItem *item )
{
	/* The tokend action sets tokend. */
	ret << "{ " << TOKEND() << " = " << TOKPREF() << " + ( " << P() << " - " << BLOCK_START() << " ); }";
}

void FsmCodeGen::INIT_ACT( ostream &ret, InlineItem *item )
{
	ret << ACT() << " = 0;";
}

void FsmCodeGen::SET_TOKSTART( ostream &ret, InlineItem *item )
{
	ret << TOKSTART() << " = " << P() << ";";
}

void FsmCodeGen::EMIT_TOKEN( ostream &ret, LangEl *token )
{
	ret << "	" << MATCHED_TOKEN() << " = " << token->id << ";\n";
}

void FsmCodeGen::LM_SWITCH( ostream &ret, InlineItem *item,
		int targState, int inFinish )
{
	ret <<
		"	switch( " << ACT() << " ) {\n";

	/* If the switch handles error then we also forced the error state. It
	 * will exist. */
	RegionImpl *region = RegionImpl::cast( item->longestMatch );
	if ( region->lmSwitchHandlesError ) {
		ret << "	case 0: " //<< P() << " = " << TOKSTART() << ";" <<
				"goto st" << redFsm->errState->id << ";\n";
	}

	for ( TokenInstanceListReg::Iter lmi = region->tokenInstanceList; lmi.lte(); lmi++ ) {
		if ( lmi->inLmSelect ) {
			assert( lmi->tokenDef->tdLangEl != 0 );
			ret << "	case " << lmi->longestMatchId << ":\n";
			EMIT_TOKEN( ret, lmi->tokenDef->tdLangEl );
			ret << "	break;\n";
		}
	}

	ret <<
		"	}\n"
		"\t"
		"	goto skip_tokpref;\n";

	skipTokprefLabelNeeded = true;
}

void FsmCodeGen::LM_ON_LAST( ostream &ret, InlineItem *item )
{
	TokenInstance *token = TokenInstance::cast( item->longestMatchPart );
	assert( token->tokenDef->tdLangEl != 0 );

	ret << "	" << P() << " += 1;\n";
	SET_TOKEND_0( ret, 0 );
	EMIT_TOKEN( ret, token->tokenDef->tdLangEl );
	ret << "	goto out;\n";
}

void FsmCodeGen::LM_ON_NEXT( ostream &ret, InlineItem *item )
{
	TokenInstance *token = TokenInstance::cast( item->longestMatchPart );
	assert( token->tokenDef->tdLangEl != 0 );

	SET_TOKEND_0( ret, 0 );
	EMIT_TOKEN( ret, token->tokenDef->tdLangEl );
	ret << "	goto out;\n";
}

void FsmCodeGen::LM_ON_LAG_BEHIND( ostream &ret, InlineItem *item )
{
	TokenInstance *token = TokenInstance::cast( item->longestMatchPart );
	assert( token->tokenDef->tdLangEl != 0 );

	EMIT_TOKEN( ret, token->tokenDef->tdLangEl );
	ret << "	goto skip_tokpref;\n";

	skipTokprefLabelNeeded = true;
}


/* Write out an inline tree structure. Walks the list and possibly calls out
 * to virtual functions than handle language specific items in the tree. */
void FsmCodeGen::INLINE_LIST( ostream &ret, InlineList *inlineList,
		int targState, bool inFinish )
{
	for ( InlineList::Iter item = *inlineList; item.lte(); item++ ) {
		switch ( item->type ) {
		case InlineItem::Text:
			assert( false );
			break;
		case InlineItem::LmSetActId:
			SET_ACT( ret, item );
			break;
		case InlineItem::LmSetTokEnd:
			SET_TOKEND( ret, item );
			break;
		case InlineItem::LmInitTokStart:
			assert( false );
			break;
		case InlineItem::LmInitAct:
			INIT_ACT( ret, item );
			break;
		case InlineItem::LmSetTokStart:
			SET_TOKSTART( ret, item );
			break;
		case InlineItem::LmSwitch:
			LM_SWITCH( ret, item, targState, inFinish );
			break;
		case InlineItem::LmOnLast:
			LM_ON_LAST( ret, item );
			break;
		case InlineItem::LmOnNext:
			LM_ON_NEXT( ret, item );
			break;
		case InlineItem::LmOnLagBehind:
			LM_ON_LAG_BEHIND( ret, item );
			break;
		default:
			assert( false );
			break;
		}
	}
}

void FsmCodeGen::ACTION( ostream &ret, GenAction *action, int targState, bool inFinish )
{
	LexAction *lexAction = reducer->lexAction( action );

	/* Write the block and close it off. */
	ret << "\t{";
	INLINE_LIST( ret, lexAction->inlineList, targState, inFinish );

	if ( lexAction->markId >= 0 )
		ret << "mark[" << lexAction->markId << "] = " << P() << ";\n";

	ret << "}\n";

}

void FsmCodeGen::emitSingleSwitch( RedStateAp *state )
{
	/* Load up the singles. */
	int numSingles = state->outSingle.length();
	RedTransEl *data = state->outSingle.data;

	if ( numSingles == 1 ) {
		/* If there is a single single key then write it out as an if. */
		out << "\tif ( " << GET_KEY() << " == " <<
				KEY(data[0].lowKey) << " )\n\t\t";

		/* Virtual function for writing the target of the transition. */
		TRANS_GOTO(data[0].value, 0) << "\n";
	}
	else if ( numSingles > 1 ) {
		/* Write out single keys in a switch if there is more than one. */
		out << "\tswitch( " << GET_KEY() << " ) {\n";

		/* Write out the single indices. */
		for ( int j = 0; j < numSingles; j++ ) {
			out << "\t\tcase " << KEY(data[j].lowKey) << ": ";
			TRANS_GOTO(data[j].value, 0) << "\n";
		}

		/* Close off the transition switch. */
		out << "\t}\n";
	}
}

void FsmCodeGen::emitRangeBSearch( RedStateAp *state, int level, int low, int high )
{
	/* Get the mid position, staying on the lower end of the range. */
	int mid = (low + high) >> 1;
	RedTransEl *data = state->outRange.data;

	/* Determine if we need to look higher or lower. */
	bool anyLower = mid > low;
	bool anyHigher = mid < high;

	/* Determine if the keys at mid are the limits of the alphabet. */
	bool limitLow = keyOps->eq( data[mid].lowKey, keyOps->minKey );
	bool limitHigh = keyOps->eq( data[mid].highKey, keyOps->maxKey );

	if ( anyLower && anyHigher ) {
		/* Can go lower and higher than mid. */
		out << TABS(level) << "if ( " << GET_KEY() << " < " <<
				KEY(data[mid].lowKey) << " ) {\n";
		emitRangeBSearch( state, level+1, low, mid-1 );
		out << TABS(level) << "} else if ( " << GET_KEY() << " > " <<
				KEY(data[mid].highKey) << " ) {\n";
		emitRangeBSearch( state, level+1, mid+1, high );
		out << TABS(level) << "} else\n";
		TRANS_GOTO(data[mid].value, level+1) << "\n";
	}
	else if ( anyLower && !anyHigher ) {
		/* Can go lower than mid but not higher. */
		out << TABS(level) << "if ( " << GET_KEY() << " < " <<
				KEY(data[mid].lowKey) << " ) {\n";
		emitRangeBSearch( state, level+1, low, mid-1 );

		/* if the higher is the highest in the alphabet then there is no
		 * sense testing it. */
		if ( limitHigh ) {
			out << TABS(level) << "} else\n";
			TRANS_GOTO(data[mid].value, level+1) << "\n";
		}
		else {
			out << TABS(level) << "} else if ( " << GET_KEY() << " <= " <<
					KEY(data[mid].highKey) << " )\n";
			TRANS_GOTO(data[mid].value, level+1) << "\n";
		}
	}
	else if ( !anyLower && anyHigher ) {
		/* Can go higher than mid but not lower. */
		out << TABS(level) << "if ( " << GET_KEY() << " > " <<
				KEY(data[mid].highKey) << " ) {\n";
		emitRangeBSearch( state, level+1, mid+1, high );

		/* If the lower end is the lowest in the alphabet then there is no
		 * sense testing it. */
		if ( limitLow ) {
			out << TABS(level) << "} else\n";
			TRANS_GOTO(data[mid].value, level+1) << "\n";
		}
		else {
			out << TABS(level) << "} else if ( " << GET_KEY() << " >= " <<
					KEY(data[mid].lowKey) << " )\n";
			TRANS_GOTO(data[mid].value, level+1) << "\n";
		}
	}
	else {
		/* Cannot go higher or lower than mid. It's mid or bust. What
		 * tests to do depends on limits of alphabet. */
		if ( !limitLow && !limitHigh ) {
			out << TABS(level) << "if ( " << KEY(data[mid].lowKey) << " <= " <<
					GET_KEY() << " && " << GET_KEY() << " <= " <<
					KEY(data[mid].highKey) << " )\n";
			TRANS_GOTO(data[mid].value, level+1) << "\n";
		}
		else if ( limitLow && !limitHigh ) {
			out << TABS(level) << "if ( " << GET_KEY() << " <= " <<
					KEY(data[mid].highKey) << " )\n";
			TRANS_GOTO(data[mid].value, level+1) << "\n";
		}
		else if ( !limitLow && limitHigh ) {
			out << TABS(level) << "if ( " << KEY(data[mid].lowKey) << " <= " <<
					GET_KEY() << " )\n";
			TRANS_GOTO(data[mid].value, level+1) << "\n";
		}
		else {
			/* Both high and low are at the limit. No tests to do. */
			TRANS_GOTO(data[mid].value, level+1) << "\n";
		}
	}
}

std::ostream &FsmCodeGen::STATE_GOTOS()
{
	for ( RedStateList::Iter st = redFsm->stateList; st.lte(); st++ ) {
		if ( st == redFsm->errState )
			STATE_GOTO_ERROR();
		else {
			/* Writing code above state gotos. */
			GOTO_HEADER( st );

			/* Try singles. */
			if ( st->outSingle.length() > 0 )
				emitSingleSwitch( st );

			/* Default case is to binary search for the ranges, if that fails then */
			if ( st->outRange.length() > 0 )
				emitRangeBSearch( st, 1, 0, st->outRange.length() - 1 );

			/* Write the default transition. */
			TRANS_GOTO( st->defTrans, 1 ) << "\n";
		}
	}
	return out;
}

void FsmCodeGen::IN_TRANS_ACTIONS( RedStateAp *state )
{
	/* Emit any transitions that have actions and that go to this state. */
	for ( int it = 0; it < state->numInConds; it++ ) {
		RedCondPair *trans = state->inConds[it];
		if ( trans->action != 0 ) {
			/* Write the label for the transition so it can be jumped to. */
			out << "tr" << trans->id << ":\n";

			/* If the action contains a next, then we must preload the current
			 * state since the action may or may not set it. */
			if ( trans->action->anyNextStmt() )
				out << "	" << CS() << " = " << trans->targ->id << ";\n";

			/* Write each action in the list. */
			for ( GenActionTable::Iter item = trans->action->key; item.lte(); item++ )
				ACTION( out, item->value, trans->targ->id, false );

			out << "\tgoto st" << trans->targ->id << ";\n";
		}
	}
}

/* Called from FsmCodeGen::STATE_GOTOS just before writing the gotos for each
 * state. */
void FsmCodeGen::GOTO_HEADER( RedStateAp *state )
{
	IN_TRANS_ACTIONS( state );

	if ( state->labelNeeded )
		out << "st" << state->id << ":\n";

	if ( state->toStateAction != 0 ) {
		/* Remember that we wrote an action. Write every action in the list. */
		for ( GenActionTable::Iter item = state->toStateAction->key; item.lte(); item++ )
			ACTION( out, item->value, state->id, false );
	}

	/* Give the state a switch case. */
	out << "case " << state->id << ":\n";

	/* Advance and test buffer pos. */
	out <<
		"	if ( ++" << P() << " == " << PE() << " )\n"
		"		goto out" << state->id << ";\n";

	if ( state->fromStateAction != 0 ) {
		/* Remember that we wrote an action. Write every action in the list. */
		for ( GenActionTable::Iter item = state->fromStateAction->key; item.lte(); item++ )
			ACTION( out, item->value, state->id, false );
	}

	/* Record the prev state if necessary. */
	if ( state->anyRegCurStateRef() )
		out << "	_ps = " << state->id << ";\n";
}

void FsmCodeGen::STATE_GOTO_ERROR()
{
	/* In the error state we need to emit some stuff that usually goes into
	 * the header. */
	RedStateAp *state = redFsm->errState;
	IN_TRANS_ACTIONS( state );

	if ( state->labelNeeded )
		out << "st" << state->id << ":\n";

	/* We do not need a case label here because the the error state is checked
	 * at the head of the loop. */

	/* Break out here. */
	out << "	goto out" << state->id << ";\n";
}


/* Emit the goto to take for a given transition. Colm's scanner transitions
 * carry no conditions. */
std::ostream &FsmCodeGen::TRANS_GOTO( RedTransAp *trans, int level )
{
	if ( trans->p.action != 0 ) {
		/* Go to the transition which will go to the state. */
		out << TABS(level) << "goto tr" << trans->p.id << ";";
	}
	else {
		/* Go directly to the target state. */
		out << TABS(level) << "goto st" << trans->p.targ->id << ";";
	}
	return out;
}

std::ostream &FsmCodeGen::EXIT_STATES()
{
	for ( RedStateList::Iter st = redFsm->stateList; st.lte(); st++ ) {
		out << "	case " << st->id << ": out" << st->id << ": ";
		RedTransAp *eofTrans = LexReducer::eofTrans( st );
		if ( eofTrans != 0 ) {
			out << "if ( " << DATA_EOF() << " ) {";
			TRANS_GOTO( eofTrans, 0 );
			out << "\n";
			out << "}";
		}

		/* Exit. */
		out << CS() << " = " << st->id << "; goto out; \n";
	}
	return out;
}

bool FsmCodeGen::anyLmSwitchError( InlineList *inlineList )
{
	for ( InlineList::Iter item = *inlineList; item.lte(); item++ ) {
		if ( item->type == InlineItem::LmSwitch &&
				item->longestMatch->lmSwitchHandlesError )
			return true;

		if ( item->children != 0 && anyLmSwitchError( item->children ) )
			return true;
	}
	return false;
}

/* Does an action the scanner takes have a longest match switch that handles
 * the error case? */
bool FsmCodeGen::anyLmSwitchError()
{
	for ( GenActionList::Iter act = reducer->actionList; act.lte(); act++ ) {
		if ( act->numRefs() > 0 &&
				anyLmSwitchError( reducer->lexAction( act )->inlineList ) )
			return true;
	}
	return false;
}

void FsmCodeGen::setLabelNeeded( RedTransAp *trans )
{
	/* If there is no action with a next statement, then the label will be
	 * needed. */
	if ( trans->p.action == 0 || !trans->p.action->anyNextStmt() )
		trans->p.targ->labelNeeded = true;
}

/* Set up labelNeeded flag for each state. */
void FsmCodeGen::setLabelsNeeded()
{
	/* Do not use all labels by default, init all labelNeeded vars to false. */
	for ( RedStateList::Iter st = redFsm->stateList; st.lte(); st++ )
		st->labelNeeded = false;

	if ( redFsm->errState != 0 && anyLmSwitchError() )
		redFsm->errState->labelNeeded = true;

	/* Walk the transitions the scanner takes and set only those that have
	 * targs. The transition set also has eof transitions the scanner never
	 * takes, so walk the states. */
	for ( RedStateList::Iter st = redFsm->stateList; st.lte(); st++ ) {
		for ( RedTransList::Iter rtel = st->outSingle; rtel.lte(); rtel++ )
			setLabelNeeded( rtel->value );
		for ( RedTransList::Iter rtel = st->outRange; rtel.lte(); rtel++ )
			setLabelNeeded( rtel->value );
		if ( st->defTrans != 0 )
			setLabelNeeded( st->defTrans );
		if ( LexReducer::eofTrans( st ) != 0 )
			setLabelNeeded( st->eofTrans );
	}

	for ( RedStateList::Iter st = redFsm->stateList; st.lte(); st++ )
		st->outNeeded = st->labelNeeded;
}

void FsmCodeGen::genAnalysis()
{
	setLabelsNeeded();
}

void FsmCodeGen::writeData()
{
	out << "#define " << START() << " " << START_STATE_ID() << "\n";
	out << "#define " << FIRST_FINAL() << " " << FIRST_FINAL_STATE() << "\n";
	out << "#define " << ERROR() << " " << ERROR_STATE() << "\n";
	out << "#define false 0\n";
	out << "#define true 1\n";
	out << "\n";

	out << "static long " << ENTRY_BY_REGION() << "[] = {\n\t";
	for ( int i = 0; i < fsmTables->num_regions; i++ ) {
		out << fsmTables->entry_by_region[i];

		if ( i < fsmTables->num_regions-1 ) {
			out << ", ";
			if ( (i+1) % 8 == 0 )
				out << "\n\t";
		}
	}
	out << "\n};\n\n";

	out <<
		"static struct fsm_tables fsmTables_start =\n"
		"{\n"
		"	0, "       /* actions */
		" 0, "         /* keyOffsets */
		" 0, "         /* transKeys */
		" 0, "         /* singleLengths */
		" 0, "         /* rangeLengths */
		" 0, "         /* indexOffsets */
		" 0, "         /* transTargsWI */
		" 0, "         /* transActionsWI */
		" 0, "         /* toStateActions */
		" 0, "         /* fromStateActions */
		" 0, "         /* eofActions */
		" 0,\n"        /* eofTargs */
		"	" << ENTRY_BY_REGION() << ",\n"

		"\n"
		"	0, "       /* numStates */
		" 0, "         /* numActions */
		" 0, "         /* numTransKeys */
		" 0, "         /* numSingleLengths */
		" 0, "         /* numRangeLengths */
		" 0, "         /* numIndexOffsets */
		" 0, "         /* numTransTargsWI */
		" 0,\n"        /* numTransActionsWI */
		"	" << fsmTables->num_regions - 1 << ",\n"
		"\n"
		"	" << START() << ",\n"
		"	" << FIRST_FINAL() << ",\n"
		"	" << ERROR() << ",\n"
		"\n"
		"	0,\n"      /* actionSwitch */
		"	0\n"       /* numActionSwitch */
		"};\n"
		"\n";
}

void FsmCodeGen::writeExec()
{
	out <<
		"static void fsm_execute( struct pda_run *pdaRun, struct input_impl *inputStream )\n"
		"{\n"
		"	" << BLOCK_START() << " = pdaRun->p;\n"
		"/*_resume:*/\n";

	if ( redFsm->errState != 0 ) {
		out <<
			"	if ( " << CS() << " == " << redFsm->errState->id << " )\n"
			"		goto out;\n";
	}

	out <<
		"	if ( " << P() << " == " << PE() << " )\n"
		"		goto out_switch;\n"
		"	--" << P() << ";\n"
		"\n"
		"	switch ( " << CS() << " )\n	{\n";
		STATE_GOTOS() <<
		"	}\n";

	out <<
		"out_switch:\n"
		"	switch ( " << CS() << " )\n	{\n";
	EXIT_STATES() <<
		"	}\n";

	out <<
		"out:\n"
		"	if ( " << P() << " != 0 )\n"
		"		" << TOKPREF() << " += " << P() << " - " << BLOCK_START() << ";\n";

	if ( skipTokprefLabelNeeded ) {
		out <<
			"skip_tokpref:\n"
			"	{}\n";
	}

	out <<
		"}\n"
		"\n";
}

void FsmCodeGen::writeCode()
{
	writeData();
	writeExec();

	/* Referenced in the runtime lib, but used only in the compiler. Probably
	 * should use the preprocessor to make these go away. */
	out <<
		"static void sendNamedLangEl( struct colm_program *prg, tree_t **tree,\n"
		"		struct pda_run *pda_run, struct input_impl *input ) { }\n"
		"static void initBindings( struct pda_run *pdaRun ) {}\n"
		"static void popBinding( struct pda_run *pdaRun, parse_tree_t *tree ) {}\n"
		"\n"
		"\n";
}

string FsmCodeGen::formatChar( Key key )
{
	ostringstream ret;

	long value = key.getVal();

	switch ( value ) {
	case '\t': ret << "\\t"; break;
	case '\n': ret << "\\n"; break;
	case '\r': ret << "\\r"; break;
	case '\\': ret << "\\\\"; break;
	default:
		if ( value >= 32 && value <= 126 )
			ret << static_cast<char>(value);
		else
			ret << "\\x" << std::hex << value;
		break;
	}

	return ret.str();
}

string FsmCodeGen::formatKey( Key key )
{
	if ( key.getVal() == ' ' )
		return "[ ]";

	return formatChar(key);
}

string FsmCodeGen::formatRange( Key lowKey, Key highKey )
{
	ostringstream ret;

	if ( keyOps->eq(lowKey, highKey) )
		return formatKey(lowKey);

	ret << "[" << formatChar(lowKey)
	    << "-" << formatChar(highKey) << "]";

	return ret.str();
}

string FsmCodeGen::formatAction( const RedAction *action )
{
	ostringstream ret;

	if ( action == 0 )
		return "";

	ret << "  [action";

	for ( GenActionTable::Iter item = action->key; item.lte(); item++ ) {
		LexAction *lexAction = reducer->lexAction(item->value);

		ret << " {";

		for ( InlineList::Iter in = *lexAction->inlineList;
				in.lte(); in++ ) {

			switch ( in->type ) {
			case InlineItem::LmSetActId:
				ret << " set-act";
				break;

			case InlineItem::LmSetTokEnd:
				ret << " tokend";
				break;

			case InlineItem::LmInitAct:
				ret << " init-act";
				break;

			case InlineItem::LmSetTokStart:
				ret << " tokstart";
				break;

			case InlineItem::LmSwitch:
				ret << " lm-switch";
				break;

			case InlineItem::LmOnLast:
				ret << " lm-last";
				break;

			case InlineItem::LmOnNext:
				ret << " lm-next";
				break;

			case InlineItem::LmOnLagBehind:
				ret << " lm-lag";
				break;

			default:
				ret << " ?";
				break;
			}
		}

		ret << " }";
	}

	ret << "]";

	return ret.str();
}

string FsmCodeGen::formatTransition( const RedTransAp *trans )
{
	ostringstream ret;

	if ( trans->p.action != 0 )
		ret << formatAction(trans->p.action);

	return ret.str();
}

void FsmCodeGen::writeDebugFsm( ostream &out )
{
	out << "Reduced lexer FSM\n";
	out << "=================\n\n";

	for ( RedStateList::Iter st = redFsm->stateList; st.lte(); st++ ) {

		if ( st == redFsm->errState ) {
			out << "State: " << st->id << "  [ERROR STATE]\n\n";
			continue;
		}
		out << "State: " << st->id << "\n";

		for ( int i = 0; i < st->outSingle.length(); i++ ) {
			RedTransEl &el = st->outSingle.data[i];
			RedTransAp *trans = el.value;

			out << "  " << formatKey(el.lowKey)
				<< " -> " << trans->p.targ->id;

			if ( trans->p.action != 0 )
				out << formatTransition(trans);

			out << "\n";
		}

		for ( int i = 0; i < st->outRange.length(); i++ ) {
			RedTransEl &el = st->outRange.data[i];
			RedTransAp *trans = el.value;

			out << "  " << formatRange(el.lowKey, el.highKey)
				<< " -> " << trans->p.targ->id;

			if ( trans->p.action != 0 )
				out << formatTransition(trans);

			out << "\n";
		}

		if ( st->defTrans != 0 ) {
			out << "  DEFAULT -> "
				<< st->defTrans->p.targ->id;

			if ( st->defTrans->p.action != 0 )
				out << formatTransition(st->defTrans);

			out << "\n";
		}

		out << "\n";
	}
}
