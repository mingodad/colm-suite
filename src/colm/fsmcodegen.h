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

#ifndef _COLM_FSMCODEGEN_H
#define _COLM_FSMCODEGEN_H

#include <assert.h>
#include <stdio.h>

#include <string>
#include <iostream>

#include "libfsm/codegen.h"

#include "compiler.h"

using std::string;
using std::ostream;

/*
 * The scanner's reduced machine. libfsm's reducer makes a GenAction for each
 * action in the graph, but a GenAction has no slot for the capture mark, and
 * its inline list no longer says which token a longest match item stands for.
 * The reducer allocates the GenActions in an array indexed by
 * Action::actionId, so a parallel array leads back to the LexAction, whose
 * inline list still has the tokens.
 */
struct LexReducer
:
	public Reducer
{
	LexReducer( Compiler *pd, FsmAp *fsm );
	~LexReducer();

	void reduce();
	fsm_tables *makeFsmTables();

	LexAction *lexAction( GenAction *genAction )
		{ return lexActions[genAction - allActions]; }

	/* libfsm gives every state an eof transition. Without eof actions it
	 * leaves the state where it is. A colm scanner state has eof actions
	 * exactly when it has an eof target, so the eof transitions with actions
	 * are the ones the scanner takes. */
	static RedTransAp *eofTrans( RedStateAp *state )
	{
		return state->eofTrans != 0 && state->eofTrans->p.action != 0 ?
				state->eofTrans : 0;
	}

private:
	Compiler *pd;
	LexAction **lexActions;
};

/*
 * Writes the goto driven scanner that reads and writes the pda_run fields.
 */
struct FsmCodeGen
:
	public CodeGen
{
	FsmCodeGen( LexReducer *reducer, ostream &out, fsm_tables *fsmTables );

	void genAnalysis();
	void writeData();
	void writeExec();

	void writeIncludes();
	void writeCode();
	void writeMain( long activeRealm );

	void writeDebugFsm( ostream &out );

protected:
	LexReducer *reducer;
	fsm_tables *fsmTables;
	bool skipTokprefLabelNeeded;

	string TABS( int level );
	string KEY( Key key );
	string GET_KEY();

	string ACCESS() { return "pdaRun->"; }

	string P() { return ACCESS() + "p"; }
	string PE() { return ACCESS() + "pe"; }
	string DATA_EOF() { return ACCESS() + "scan_eof"; }

	string CS() { return ACCESS() + "fsm_cs"; }
	string TOKSTART() { return ACCESS() + "tokstart"; }
	string TOKEND() { return ACCESS() + "tokend"; }
	string BLOCK_START() { return ACCESS() + "start"; }
	string TOKPREF() { return ACCESS() + "tokpref"; }
	string ACT() { return ACCESS() + "act"; }
	string MATCHED_TOKEN() { return ACCESS() + "matched_token"; }

	string ENTRY_BY_REGION() { return DATA_PREFIX() + "entry_by_region"; }

	void ACTION( ostream &ret, GenAction *action, int targState, bool inFinish );
	void INLINE_LIST( ostream &ret, InlineList *inlineList,
			int targState, bool inFinish );
	void LM_SWITCH( ostream &ret, InlineItem *item, int targState, int inFinish );
	void SET_ACT( ostream &ret, InlineItem *item );
	void INIT_ACT( ostream &ret, InlineItem *item );
	void SET_TOKSTART( ostream &ret, InlineItem *item );
	void SET_TOKEND( ostream &ret, InlineItem *item );
	void SET_TOKEND_0( ostream &ret, InlineItem *item );
	void LM_ON_LAST( ostream &ret, InlineItem *item );
	void LM_ON_NEXT( ostream &ret, InlineItem *item );
	void LM_ON_LAG_BEHIND( ostream &ret, InlineItem *item );
	void EMIT_TOKEN( ostream &ret, LangEl *token );

	std::ostream &STATE_GOTOS();
	void emitSingleSwitch( RedStateAp *state );
	void emitRangeBSearch( RedStateAp *state, int level, int low, int high );
	std::ostream &EXIT_STATES();
	std::ostream &TRANS_GOTO( RedTransAp *trans, int level );

	/* Called from STATE_GOTOS just before writing the gotos for each
	 * state. */
	void IN_TRANS_ACTIONS( RedStateAp *state );
	void GOTO_HEADER( RedStateAp *state );
	void STATE_GOTO_ERROR();

	bool anyLmSwitchError( InlineList *inlineList );
	bool anyLmSwitchError();

	/* Set up labelNeeded flag for each state. */
	void setLabelNeeded( RedTransAp *trans );
	void setLabelsNeeded();

	/* Colm's scanner actions contain none of these. */
	void GOTO( ostream &ret, int gotoDest, bool inFinish ) { assert( false ); }
	void CALL( ostream &ret, int callDest, int targState, bool inFinish ) { assert( false ); }
	void NCALL( ostream &ret, int callDest, int targState, bool inFinish ) { assert( false ); }
	void NEXT( ostream &ret, int nextDest, bool inFinish ) { assert( false ); }
	void GOTO_EXPR( ostream &ret, GenInlineItem *ilItem, bool inFinish ) { assert( false ); }
	void NEXT_EXPR( ostream &ret, GenInlineItem *ilItem, bool inFinish ) { assert( false ); }
	void CALL_EXPR( ostream &ret, GenInlineItem *ilItem, int targState, bool inFinish )
		{ assert( false ); }
	void NCALL_EXPR( ostream &ret, GenInlineItem *ilItem, int targState, bool inFinish )
		{ assert( false ); }
	void RET( ostream &ret, bool inFinish ) { assert( false ); }
	void NRET( ostream &ret, bool inFinish ) { assert( false ); }
	void BREAK( ostream &ret, int targState, bool csForced ) { assert( false ); }
	void NBREAK( ostream &ret, int targState, bool csForced ) { assert( false ); }
	void CURS( ostream &ret, bool inFinish ) { assert( false ); }
	void TARGS( ostream &ret, bool inFinish, int targState ) { assert( false ); }
	void NFA_POP() { assert( false ); }

	string formatChar( Key key );
	string formatClassChar( int c );
	string formatKey( Key key );
	string formatAction( const RedAction *action );
	string formatTransition( const RedTransAp *trans );
	string formatRange( Key low, Key high );
};

#endif /* _COLM_FSMCODEGEN_H */

