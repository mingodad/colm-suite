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

#include "global.h"
#define EOF_REGION 0

#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <assert.h>

#include <iostream>

/* Dumping the fsm. */
#include <mergesort.h>

/* Parsing. */
#include "compiler.h"
#include "pdacodegen.h"

using std::endl;
using std::cerr;
using std::cout;

char startDefName[] = "start";

extern "C" tree_t **internal_host_call( program_t *prg, long code, tree_t **sp )
{
	return 0;
}

extern "C" void internal_commit_reduce_forward( program_t *prg, tree_t **root,
		struct pda_run *pda_run, parse_tree_t *pt )
{
	commit_clear_parse_tree( prg, root, pda_run, pt->child );
}

extern "C" long internal_commit_union_sz( int reducer )
{
	return 0;
}

extern "C" void internal_init_need()
{
}

extern "C" int internal_reducer_need_tok( program_t *prg, struct pda_run *, int id )
{
	return 3;
}

extern "C" int internal_reducer_need_ign( program_t *prg, struct pda_run * )
{
	return 3;
}

/* Count the transitions in the fsm by walking the state list. */
int countTransitions( PdaGraph *fsm )
{
	int numTrans = 0;
	PdaState *state = fsm->stateList.head;
	while ( state != 0 ) {
		numTrans += state->transMap.length();
		state = state->next;
	}
	return numTrans;
}

LangEl::LangEl( Namespace *nspace, const String &name, Type type )
:
	nspace(nspace),
	name(name),
	lit(name),
	type(type),
	id(-1),
	numAppearances(0),
	commit(false),
	isIgnore(false),
	reduceFirst(false),
	isLiteral(false),
	isRepeat(false),
	isList(false),
	isOpt(false),
	parseStop(false),
	isEOF(false),
	leftRecursive(false),
	repeatOf(0),
	tokenDef(0),
	rootDef(0),
	termDup(0),
	eofLel(0),
	pdaGraph(0),
	pdaTables(0),
	transBlock(0),
	objectDef(0),
	thisSize(0),
	ofiOffset(0),
	parserId(-1),
	predType(PredNone),
	predValue(0),
	contextDef(0),
	contextIn(0),
	noPreIgnore(false),
	noPostIgnore(false),
	isZero(false)
{
}

PdaGraph *ProdElList::walk( Compiler *pd, Production *prod )
{
	PdaGraph *prodFsm = new PdaGraph();
	PdaState *last = prodFsm->addState();
	prodFsm->setStartState( last );

	int prodLength = 0;
	for ( Iter prodEl = first(); prodEl.lte(); prodEl++, prodLength++ ) {
		//PdaGraph *itemFsm = prodEl->walk( pd );
		long value = prodEl->langEl->id;

		PdaState *newState = prodFsm->addState();
		PdaTrans *newTrans = prodFsm->appendNewTrans( last, newState, value, value );

		newTrans->isShift = true;
		newTrans->shiftPrior = prodEl->priorVal;
		//cerr << "PRIOR VAL: " << newTrans->shiftPrior << endl;

		if ( prodEl->commit ) {
			//cout << "COMMIT: inserting commit of length: " << pd->prodLength << endl;
			/* Insert the commit into transitions out of last */
			for ( TransMap::Iter trans = last->transMap; trans.lte(); trans++ )
				trans->value->commits.insert( prodLength );
		}

		last = newState;
	}

	/* Make the last state the final state. */
	prodFsm->setFinState( last );
	return prodFsm;
}


ProdElList *Compiler::makeProdElList( LangEl *langEl )
{
	ProdElList *prodElList = new ProdElList();
	UniqueType *uniqueType = findUniqueType( TYPE_TREE, langEl );
	TypeRef *typeRef = TypeRef::cons( internal, uniqueType );
	prodElList->append( new ProdEl( internal, typeRef ) );
	prodElList->tail->langEl = langEl;
	return prodElList;
}

void Compiler::makeDefinitionNames()
{
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		int prodNum = 1;
		for ( LelProdList::Iter def = lel->prodList; def.lte(); def++ ) {
			def->data.setAs( lel->name.length() + 32, "%s-%i",
					lel->name.data, prodNum++ );
		}
	}
}

/* Make sure there there are no language elements whose type is unkonwn. This
 * can happen when an id is used on the rhs of a definition but is not defined
 * as anything. */
void Compiler::noUndefindLangEls()
{
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		if ( lel->type == LangEl::Unknown )
			error() << "'" << lel->name << "' was not defined as anything" << endp;
	}
}

void Compiler::makeLangElIds()
{
	/* The first id 0 is reserved for the stack sentinal. A negative id means
	 * error to the parsing function, inducing backtracking. */
	nextLelId = 1;

	/* First pass assigns to the user terminals. */
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		/* Must be a term, and not any of the special reserved terminals.
		 * Remember if the non terminal is a user non terminal. */
		if ( lel->type == LangEl::Term &&
				!lel->isEOF &&
				lel != errorLangEl &&
				lel != noTokenLangEl )
		{
			lel->id = nextLelId++;
		}
	}

	//eofLangEl->id = nextLelId++;
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		/* Must be a term, and not any of the special reserved terminals.
		 * Remember if the non terminal is a user non terminal. */
		if ( lel->isEOF )
			lel->id = nextLelId++;
	}

	/* Next assign to the eof notoken, which we always create. */
	noTokenLangEl->id = nextLelId++;

	/* Possibly assign to the error language element. */
	if ( errorLangEl != 0 )
		errorLangEl->id = nextLelId++;

	/* Save this for the code generation. */
	firstNonTermId = nextLelId;

	/* A third and final pass assigns to everything else. */
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		/* Anything else not yet assigned gets assigned now. */
		if ( lel->id < 0 )
			lel->id = nextLelId++;
	}

	assert( ptrLangEl->id == LEL_ID_PTR );
	assert( strLangEl->id == LEL_ID_STR );
	assert( ignoreLangEl->id == LEL_ID_IGNORE );
}

void Compiler::makeStructElIds()
{
	firstStructElId = nextLelId;

	/* Start at the next lang el id and go up from there. Using disjoint sets
	 * allows us to verify that a tree is a tree and struct is a struct because
	 * the ID field is at the same offset. */
	int nextId = nextLelId;
	for ( StructElList::Iter sel = structEls; sel.lte(); sel++ )
		sel->id = nextId++;

	structInbuiltId = nextId++;
	structInputId = nextId++;
	structStreamId = nextId++;
}

void Compiler::refNameSpace( LangEl *lel, Namespace *nspace )
{
	if ( nspace == rootNamespace ) {
		lel->refName = "::" + lel->refName;
		return;
	}

	lel->refName = nspace->name + "::" + lel->refName;
	lel->declName = nspace->name + "::" + lel->declName;
	lel->xmlTag = nspace->name + "::" + lel->xmlTag;
	refNameSpace( lel, nspace->parentNamespace );
}

void Compiler::makeLangElNames()
{
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		lel->fullName = lel->name;
		lel->fullLit = lel->lit;
		lel->refName = lel->lit;
		lel->declName = lel->lit;
		lel->xmlTag = lel->name;

		/* If there is also a namespace next to the type, we add a prefix to
		 * the type. It's not convenient to name C++ classes the same as a
		 * namespace in the same scope. We don't want to restrict colm, so we
		 * add a workaround for the least-common case. The type gets t_ prefix.
		 * */
		Namespace *nspace = lel->nspace->findNamespace( lel->name );
		if ( nspace != 0 ) {
			lel->refName = "t_" + lel->refName;
			lel->fullName = "t_" + lel->fullName;
			lel->declName = "t_" + lel->declName;
			lel->xmlTag = "t_" + lel->xmlTag;
		}

		refNameSpace( lel, lel->nspace );
	}
}

/* Set up dot sets, shift info, and prod sets. */
void Compiler::makeProdFsms()
{
	/* There are two items in the index for each production (high and low). */
	int indexLen = prodList.length() * 2;
	dotItemIndex.setAsNew( indexLen );
	int dsiLow = 0, indexPos = 0;

	/* Build FSMs for all production language elements. */
	for ( ProdList::Iter prod = prodList; prod.lte(); prod++ )
		prod->fsm = prod->prodElList->walk( this, prod );

	makeNonTermFirstSets();
	makeFirstSets();

	/* Build FSMs for all production language elements. */
	for ( ProdList::Iter prod = prodList; prod.lte(); prod++ ) {
		if ( addUniqueEmptyProductions ) {
			/* This must be re-implemented. */
			assert( false );
			//if ( !prod->isLeftRec && prod->uniqueEmptyLeader != 0 ) {
			//	PdaGraph *emptyLeader = prod->uniqueEmptyLeader->walk( this );
			//	emptyLeader->concatOp( prod->fsm );
			//	prod->fsm = emptyLeader;
			//}
		}

		/* Compute the machine's length. */
		prod->fsmLength = prod->fsm->fsmLength( );

		/* Productions have a unique production id for each final state.
		 * This lets us use a production length specific to each final state.
		 * Start states are always isolated therefore if the start state is
		 * final then reductions from it will always have a fixed production
		 * length. This is a simple method for determining the length
		 * of zero-length derivations when reducing. */

		/* Number of dot items needed for the production is elements + 1
		 * because the dot can be before the first and after the last element. */
		int numForProd = prod->fsm->stateList.length() + 1;

		/* Remember the first dot ID for this production. */
		prod->firstDotId = dsiLow;

		/* Set up the low and high values in the index for this production. */
		dotItemIndex.data[indexPos].key = dsiLow;
		dotItemIndex.data[indexPos].value = prod;
		dotItemIndex.data[indexPos+1].key = dsiLow + numForProd - 1;
		dotItemIndex.data[indexPos+1].value = prod;

		int dsi = dsiLow;
		for ( PdaStateList::Iter state = prod->fsm->stateList; state.lte(); state++, dsi++ ) {
			/* All transitions are shifts. */
			for ( TransMap::Iter out = state->transMap; out.lte(); out++ )
				assert( out->value->isShift );

			state->dotSet.insert( dsi );
		}

		/* Move over the production. */
		dsiLow += numForProd;
		indexPos += 2;

		if ( prod->prodCommit ) {
			for ( PdaStateSet::Iter fin = prod->fsm->finStateSet; fin.lte(); fin++ ) {
				int length = prod->fsmLength;
				//cerr << "PENDING COMMIT IN FINAL STATE of " << prod->prodId <<
				//		" with len: " << length << endl;
				(*fin)->pendingCommits.insert( ProdIdPair( prod->prodId, length ) );
			}
		}
	}

	/* Make the final state specific prod id to prod id mapping. */
	prodIdIndex = new Production*[prodList.length()];
	for ( ProdList::Iter prod = prodList; prod.lte(); prod++ )
		prodIdIndex[prod->prodId] = prod;
}

/* Want the first set of over src. If the first set contains epsilon, go over
 * it and over tab. If overSrc is the end of the production, find the follow
 * from the table, taking only the characters on which the parent is reduced.
 * */
void Compiler::findFollow( AlphSet &result, PdaState *overTab,
		PdaState *overSrc, Production *parentDef )
{
	if ( overSrc->isFinState() ) {
		assert( overSrc->transMap.length() == 0 );

		/* At the end of the production. Turn to the table. */
		long redCode = makeReduceCode( parentDef->prodId, false );
		for ( TransMap::Iter tabTrans = overTab->transMap; tabTrans.lte(); tabTrans++ ) {
			for ( ActDataList::Iter adl = tabTrans->value->actions; adl.lte(); adl++ ) {
				if ( *adl == redCode )
					result.insert( tabTrans->key );
			}
		}
	}
	else {
		/* Get the first set of the item. If the first set contains epsilon
		 * then move over overSrc and overTab and recurse. */
		assert( overSrc->transMap.length() == 1 );
		TransMap::Iter pastTrans = overSrc->transMap;

		LangEl *langEl = langElIndex[pastTrans->key];
		if ( langEl != 0 && langEl->type == LangEl::NonTerm ) {
			bool hasEpsilon = false;
			for ( LelProdList::Iter def = langEl->prodList; def.lte(); def++ ) {
				result.insert( def->firstSet );

				if ( def->firstSet.find( -1 ) )
					hasEpsilon = true;
			}

			/* Find the equivalent state in the parser. */
			if ( hasEpsilon ) {
				PdaTrans *tabTrans = overTab->findTrans( pastTrans->key );
				findFollow( result, tabTrans->toState,
						pastTrans->value->toState, parentDef );
			}

			/* Now possibly the dup. */
			if ( langEl->termDup != 0 )
				result.insert( langEl->termDup->id );
		}
		else {
			result.insert( pastTrans->key );
		}
	}
}

PdaState *Compiler::followProd( PdaState *tabState, PdaState *prodState )
{
	while ( prodState->transMap.length() == 1 ) {
		TransMap::Iter prodTrans = prodState->transMap;
		PdaTrans *tabTrans = tabState->findTrans( prodTrans->key );
		prodState = prodTrans->value->toState;
		tabState = tabTrans->toState;
	}
	return tabState;
}

void Compiler::trySetTime( PdaTrans *trans, long code, long &time )
{
	/* Find the item. */
	for ( ActDataList::Iter adl = trans->actions; adl.lte(); adl++ ) {
		if ( *adl == code ) {
			/* If the time of the shift is not already set, set it. */
			if ( trans->actOrds[adl.pos()] == 0 ) {
				//cerr << "setting time: state = " << tabState->stateNum
				//		<< ", trans = " << tabTrans->lowKey
				//		<< ", time = " << time << endl;
				trans->actOrds[adl.pos()] = time++;
			}
			break;
		}
	}
}

/* Go down a defintiion and then handle the follow actions. */
void Compiler::pdaOrderFollow( LangEl *rootEl, PdaState *tabState,
		PdaTrans *tabTrans, PdaTrans *srcTrans, Production *parentDef,
		Production *definition, long &time )
{
	/* We need the follow from tabState/srcState over the definition we are
	 * currently processing. */
	PdaState *overTab = tabTrans->toState;
	PdaState *overSrc = srcTrans->toState;

	AlphSet alphSet;
	if ( parentDef == rootEl->rootDef )
		alphSet.insert( rootEl->eofLel->id );
	else
		findFollow( alphSet, overTab, overSrc, parentDef );

	/* Now follow the production to find out where it expands to. */
	PdaState *expandToState = followProd( tabState, definition->fsm->startState );

	/* Find the reduce item. */
	long redCode = makeReduceCode( definition->prodId, false );

	for ( TransMap::Iter tt = expandToState->transMap; tt.lte(); tt++ ) {
		if ( alphSet.find( tt->key ) ) {
			trySetTime( tt->value, redCode, time );

			/* If the items token region is not recorded in the state, do it now. */
			addRegion( expandToState, tt->value, tt->key,
					tt->value->noPreIgnore, tt->value->noPostIgnore );
		}
	}
}

bool regionVectHas( RegionVect &regVect, TokenRegion *region )
{
	for ( RegionVect::Iter trvi = regVect; trvi.lte(); trvi++ ) {
		if ( *trvi == region )
			return true;
	}
	return false;
}

void Compiler::addRegion( PdaState *tabState, PdaTrans *tabTrans,
		long pdaKey, bool noPreIgnore, bool noPostIgnore )
{
	LangEl *langEl = langElIndex[pdaKey];
	if ( langEl != 0 && langEl->type == LangEl::Term ) {
		TokenRegion *region = 0;
		RegionSet *regionSet = 0;

		/* If it is not the eof, then use the region associated
		 * with the token definition. */
		if ( langEl->isZero ) {
			region = langEl->tokenDef->regionSet->collectIgnore;
			regionSet = langEl->tokenDef->regionSet;
		}
		else if ( !langEl->isEOF && langEl->tokenDef != 0 ) {
			region = langEl->tokenDef->regionSet->tokenIgnore;
			regionSet = langEl->tokenDef->regionSet;
		}

		if ( region != 0 ) {
			/* region. */
			TokenRegion *scanRegion = region;

			if ( langEl->noPreIgnore )
				scanRegion = regionSet->tokenOnly;

			if ( !regionVectHas( tabState->regions, scanRegion ) )
				tabState->regions.append( scanRegion );

			/* Pre-region of to state */
			PdaState *toState = tabTrans->toState;
			if ( !langEl->noPostIgnore &&
					regionSet->ignoreOnly != 0 &&
					!regionVectHas( toState->preRegions, regionSet->ignoreOnly ) )
			{
				toState->preRegions.append( regionSet->ignoreOnly );
			}
		}
	}
}

#if 0
    orderState( tabState, prodState, time ):
        if not tabState.dotSet.find( prodState.dotID )
            tabState.dotSet.insert( prodState.dotID )
            tabTrans = tabState.findMatchingTransition( prodState.getTransition() )

            if tabTrans is NonTerminal:
                for production in tabTrans.nonTerm.prodList:
                    orderState( tabState, production.startState, time )

                    for all expandToState in tabTrans.expandToStates:
                        for all followTrans in expandToState.transList
                            reduceAction = findAction( production.reduction )
                            if reduceAction.time is unset:
                                reduceAction.time = time++
                            end
                        end
                    end
                end
            end

            shiftAction = tabTrans.findAction( shift )
            if shiftAction.time is unset:
                shiftAction.time = time++
            end

            orderState( tabTrans.toState, prodTrans.toState, time )
        end
    end

    orderState( parseTable.startState, startProduction.startState, 1 )
#endif

void Compiler::pdaOrderProd( LangEl *rootEl, PdaState *tabState,
	PdaState *srcState, Production *parentDef, long &time )
{
	assert( srcState->dotSet.length() == 1 );
	if ( tabState->dotSet2.find( srcState->dotSet[0] ) )
		return;
	tabState->dotSet2.insert( srcState->dotSet[0] );

	assert( srcState->transMap.length() == 0 || srcState->transMap.length() == 1 );

	if ( srcState->transMap.length() == 1 ) {
		TransMap::Iter srcTrans = srcState->transMap;

		/* Find the equivalent state in the parser. */
		PdaTrans *tabTrans = tabState->findTrans( srcTrans->key );

		/* Recurse into the transition if it is a non-terminal. */
		LangEl *langEl = langElIndex[srcTrans->key];
		if ( langEl != 0 ) {
			if ( langEl->reduceFirst ) {
				/* Use a shortest match ordering for the contents of this
				 * nonterminal. Does follows for all productions first, then
				 * goes down the productions. */
				for ( LelProdList::Iter expDef = langEl->prodList; expDef.lte(); expDef++ ) {
					pdaOrderFollow( rootEl, tabState, tabTrans, srcTrans->value,
							parentDef, expDef, time );
				}
				for ( LelProdList::Iter expDef = langEl->prodList; expDef.lte(); expDef++ )
					pdaOrderProd( rootEl, tabState, expDef->fsm->startState, expDef, time );

			}
			else {
				/* The default action ordering. For each prod, goes down the
				 * prod then sets the follow before going to the next prod. */
				for ( LelProdList::Iter expDef = langEl->prodList; expDef.lte(); expDef++ ) {
					pdaOrderProd( rootEl, tabState, expDef->fsm->startState, expDef, time );

					pdaOrderFollow( rootEl, tabState, tabTrans, srcTrans->value,
							parentDef, expDef, time );
				}
			}
		}

		trySetTime( tabTrans, SHIFT_CODE, time );

		/* Now possibly for the dup. */
		if ( langEl != 0 && langEl->termDup != 0 ) {
			PdaTrans *dupTrans = tabState->findTrans( langEl->termDup->id );
			trySetTime( dupTrans, SHIFT_CODE, time );
		}

		/* If the items token region is not recorded in the state, do it now. */
		addRegion( tabState, tabTrans, srcTrans->key,
				srcTrans->value->noPreIgnore, srcTrans->value->noPostIgnore );

		/* Go over one in the production. */
		pdaOrderProd( rootEl, tabTrans->toState,
				srcTrans->value->toState, parentDef, time );
	}
}

void Compiler::pdaActionOrder( PdaGraph *pdaGraph, LangElSet &parserEls )
{
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		assert( (state->stateBits & SB_ISMARKED) == 0 );

		/* Traverse the src state's transitions. */
		long last = 0;
		for ( TransMap::Iter trans = state->transMap; trans.lte(); trans++ ) {
			if ( ! trans.first() )
				assert( last < trans->key );
			last = trans->key;
		}
	}

	/* Compute the action orderings, record the max value. */
	long time = 1;
	for ( LangElSet::Iter pe = parserEls; pe.lte(); pe++ ) {
		PdaState *startState = (*pe)->rootDef->fsm->startState;
		pdaOrderProd( *pe, (*pe)->startState, startState, (*pe)->rootDef, time );

		/* Walk over the start lang el and set the time for shift of
		 * the eof action that completes the parse. */
		PdaTrans *overStart = (*pe)->startState->findTrans( (*pe)->id );
		PdaTrans *eofTrans = overStart->toState->findTrans( (*pe)->eofLel->id );
		eofTrans->actOrds[0] = time++;
	}

	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		if ( state->regions.length() == 0 ) {
			for ( TransMap::Iter tel = state->transMap; tel.lte(); tel++ ) {
				/* There are no regions and EOF leaves the state. Add the eof
				 * token region. */
				PdaTrans *trans = tel->value;
				LangEl *lel = langElIndex[trans->lowKey];
				if ( lel != 0 && lel->isEOF )
					state->regions.append( EOF_REGION );
			}
		}
	}

	///* Warn about states with empty token region lists. */
	//for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
	//	if ( state->regions.length() == 0 ) {
	//		warning() << "state has an empty token region, state: " <<
	//			state->stateNum << endl;
	//	}
	//}

	/* Some actions may not have an ordering. I believe these to be actions
	 * that result in a parse error and they arise because the state tables
	 * are LALR(1) but the action ordering is LR(1). LALR(1) causes some
	 * reductions that lead nowhere. */
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		assert( CmpDotSet::compare( state->dotSet, state->dotSet2 ) == 0 );
		for ( TransMap::Iter tel = state->transMap; tel.lte(); tel++ ) {
			PdaTrans *trans = tel->value;
			/* Check every action has an ordering. */
			for ( ActDataList::Iter adl = trans->actOrds; adl.lte(); adl++ ) {
				if ( *adl == 0 )
					*adl = time++;
			}
		}
	}
}

void Compiler::advanceReductions( PdaGraph *pdaGraph )
{
	/* Loop all states. */
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		if ( !state->advanceReductions )
			continue;

		bool outHasShift = false;
		ReductionMap outReds;
		LongSet outCommits;
		for ( TransMap::Iter out = state->transMap; out.lte(); out++ ) {
			/* Get the transition from the trans el. */
			if ( out->value->isShift )
				outHasShift = true;
			outReds.insert( out->value->reductions );
			outCommits.insert( out->value->commits );
		}

		bool inHasShift = false;
		ReductionMap inReds;
		for ( PdaTransInList::Iter in = state->inRange; in.lte(); in++ ) {
			/* Get the transition from the trans el. */
			if ( in->isShift )
				inHasShift = true;
			inReds.insert( in->reductions );
		}

		if ( !outHasShift && outReds.length() == 1 &&
				inHasShift && inReds.length() == 0 )
		{
			//cerr << "moving reduction to shift" << endl;

			/* Move the reduction to all in transitions. */
			for ( PdaTransInList::Iter in = state->inRange; in.lte(); in++ ) {
				assert( in->actions.length() == 1 );
				assert( in->actions[0] == SHIFT_CODE );
				in->actions[0] = makeReduceCode( outReds[0].key, true );
				in->afterShiftCommits.insert( outCommits );
			}

			/*
			 * Remove all transitions out of the state.
			 */

			/* Detach out range transitions. */
			for ( TransMap::Iter trans = state->transMap; trans.lte(); trans++ ) {
				pdaGraph->detachTrans( state, trans->value->toState, trans->value );
				delete trans->value;
			}
			state->transMap.empty();

			/* Redirect all the in transitions to the actionDestState. */
			pdaGraph->inTransMove( actionDestState, state );
		}
	}

	pdaGraph->removeUnreachableStates();
}

int Compiler::prodLength( Production *prod )
{
    int len = 0;

    for ( ProdElList::Iter el = *prod->prodElList;
          el.lte(); el++ )
    {
        len++;
    }

    return len;
}

void Compiler::printLocSuffix( std::ostream &out, Production *prod )
{
	if ( prod != 0 && prod->loc.fileName != 0 )
		out << "  [" << locFileName( prod->loc ) << ":" << prod->loc.line << "]";
}

void Compiler::printDotItemForConflict( std::ostream &out, long dot, const char *label )
{
	Production *prod = prodForDot( dot );
	if ( prod == 0 ) {
		out << "      " << label
			 << ": <unknown dot " << dot << ">\n";
		return;
	}

	int dotPos = dotPosForDot( dot );

	out << "      " << label << ": "
		 << prod->prodName->name << " -> ";

	int pos = 0;

	for ( ProdElList::Iter el = *prod->prodElList;
		  el.lte(); el++, pos++ )
	{
		if ( pos == dotPos )
			out << ". ";

		if ( el->langEl != 0 )
			out << el->langEl->lit;
		else
			out << "?";

		out << " ";
	}

	if ( pos == dotPos )
		out << ".";

	printLocSuffix( out, prod );

	out << "\n";
}

void Compiler::printConflictDetails( std::ostream &out, PdaState *state, PdaTrans *trans )
{
	LangEl *lel = langElIndex[trans->lowKey];

	bool hasShift = false;
	int reduceCount = 0;

	for ( ActDataList::Iter act = trans->actions;
		  act.lte(); act++ )
	{
		switch ( *act & SHIFT_REDUCE_MASK ) {
		case SHIFT_CODE:
			hasShift = true;
			break;

		case REDUCE_CODE:
			reduceCount++;
			break;

		case SHIFT_REDUCE_CODE:
			break;
		}
	}

	bool hasConflict = (hasShift && reduceCount > 0) || (reduceCount > 1);

	if ( !hasConflict )
		return;

	out << "\n  CONFLICT on ";
	if ( lel != 0 )
		out << "'" << lel->lit << "'";
	else
		out << "<" << trans->lowKey << ">";

	out << "\n";

	for ( ActDataList::Iter act = trans->actions;
		  act.lte(); act++ )
	{
		switch ( *act & SHIFT_REDUCE_MASK ) {
		case SHIFT_CODE: {
			out << "\n    SHIFT to state "
				 << trans->toState->stateNum << "\n";

			bool found = false;

			for ( DotSet::Iter dot = state->dotSet;
				  dot.lte(); dot++ )
			{
				Production *prod = prodForDot( *dot );
				if ( prod == 0 )
					continue;

				int dotPos = dotPosForDot( *dot );
				int pos = 0;

				for ( ProdElList::Iter el = *prod->prodElList;
					  el.lte(); el++, pos++ )
				{
					if ( pos != dotPos )
						continue;

					if ( lel != 0 && el->langEl == lel ) {
						printDotItemForConflict( out,
							*dot, "Candidate item" );
						found = true;
					}

					break;
				}
			}
			break;
		}

		case REDUCE_CODE: {
			Production *target =
				prodIdIndex[GET_SHIFT_REDUCE(*act)];

			out << "\n    REDUCE "
				 << target->prodName->name << "-"
				 << target->prodNum;

			printLocSuffix( out, target );

			out << "\n";

			bool found = false;
			int targetLength = prodLength( target );

			for ( DotSet::Iter dot = state->dotSet;
				  dot.lte(); dot++ )
			{
				Production *prod = prodForDot( *dot );
				if ( prod != target )
					continue;

				if ( dotPosForDot( *dot ) == targetLength ) {
					printDotItemForConflict( out,
						*dot, "Completed item" );
					found = true;
				}
			}

			if ( !found )
				out << "      No completed item found in state.\n";

			out << "      Action terminal: ";
			if ( lel != 0 )
				out << "'" << lel->lit << "'";
			else
				out << trans->lowKey;
			out << "\n";

			break;
		}

		case SHIFT_REDUCE_CODE: {
			Production *prod =
				prodIdIndex[GET_SHIFT_REDUCE(*act)];

			out << "\n    SHIFT-REDUCE "
				 << prod->prodName->name << "-"
				 << prod->prodNum;

			printLocSuffix( out, prod );

			out << "\n";
			break;
        }
        }
    }
}

Production *Compiler::prodForDot( long dot )
{
	Production *result = 0;

	for ( ProdList::Iter prod = prodList; prod.lte(); prod++ ) {
		long low = prod->firstDotId;
		long high = low + prod->fsm->stateList.length();

		if ( dot >= low && dot <= high ) {
			result = &*prod;
			break;
        }
    }

    return result;
}

int Compiler::dotPosForDot( long dot )
{
    Production *prod = prodForDot( dot );
    if ( prod == 0 )
        return -1;

    return (int)(dot - prod->firstDotId);
}

void Compiler::recordPdaConflict( PdaTrans *trans )
{
    int cls = pdaConflictClass( trans );
    trans->conflictRawKind = cls;

    switch ( cls ) {
    case 1:
        pdaShiftReduceConflicts++;
        break;

    case 2:
        pdaReduceReduceConflicts++;
        break;
    }
}

/* Classify the remaining actions of a transition. Returns 1 for a shift/reduce
 * conflict, 2 for a reduce/reduce conflict and 0 for none. This is the single
 * classifier used both for the raw counts (before precedence) and for the
 * recount of what survived precedence resolution. */
int Compiler::pdaConflictClass( PdaTrans *trans )
{
    bool hasShift = false;
    int reduceCount = 0;

    for ( ActDataList::Iter act = trans->actions; act.lte(); act++ ) {
        switch ( *act & SHIFT_REDUCE_MASK ) {
        case SHIFT_CODE:
            hasShift = true;
            break;

        case REDUCE_CODE:
            reduceCount++;
            break;

        case SHIFT_REDUCE_CODE:
            /* Shift-reduces are already combined actions. */
            break;
        }
    }

    if ( hasShift && reduceCount > 0 )
        return 1;
    else if ( reduceCount > 1 )
        return 2;
    return 0;
}

void Compiler::countPdaConflicts( PdaGraph *pdaGraph,
        long &shiftReduce, long &reduceReduce )
{
    shiftReduce = 0;
    reduceReduce = 0;

    for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
        for ( TransMap::Iter tr = state->transMap; tr.lte(); tr++ ) {
            switch ( pdaConflictClass( tr->value ) ) {
            case 1:
                shiftReduce++;
                break;

            case 2:
                reduceReduce++;
                break;
            }
        }
    }
}

/* Count distinct conflict sites: one per (state, conflict kind, shift target,
 * action set). The report prints one entry per site, covering all the
 * lookahead tokens that share it, so this is the figure that reads as "number
 * of decisions to make" rather than the per-lookahead pair counts. */
long Compiler::countPdaConflictEntries( PdaGraph *pdaGraph )
{
	long entries = 0;

	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		for ( TransMap::Iter tr = state->transMap; tr.lte(); tr++ ) {
			PdaTrans *trans = tr->value;
			int cls = pdaConflictClass( trans );
			if ( cls == 0 )
				continue;

			/* Count only the first transition in the state with this shape. */
			bool first = true;
			for ( TransMap::Iter prev = state->transMap;
					prev.lte() && prev->value != trans; prev++ ) {
				PdaTrans *p = prev->value;
				if ( pdaConflictClass( p ) != cls || p->toState != trans->toState )
					continue;
				if ( p->actions.length() != trans->actions.length() )
					continue;

				bool same = true;
				for ( int k = 0; k < trans->actions.length(); k++ ) {
					if ( p->actions[k] != trans->actions[k] ) {
						same = false;
						break;
					}
				}
				if ( same ) {
					first = false;
					break;
				}
			}

			if ( first )
				entries++;
		}
	}

	return entries;
}

bool Compiler::pdaStateHasConflict( PdaState *state )
{
	for ( TransMap::Iter tr = state->transMap; tr.lte(); tr++ ) {
		if ( pdaConflictClass( tr->value ) != 0 )
			return true;
	}
	return false;
}

/* Format a single action code. toStateNum supplies the shift target because
 * the action code itself does not carry it. */
void Compiler::printPdaAction( std::ostream &out, long act, long toStateNum )
{
	switch ( act & SHIFT_REDUCE_MASK ) {
	case SHIFT_CODE:
		out << "shift " << toStateNum;
		break;

	case REDUCE_CODE: {
		Production *prod = prodIdIndex[GET_SHIFT_REDUCE(act)];
		out << "reduce " << prod->prodName->name << "-" << prod->prodNum;
		break;
	}

	case SHIFT_REDUCE_CODE: {
		Production *prod = prodIdIndex[GET_SHIFT_REDUCE(act)];
		out << "shift-reduce " << prod->prodName->name << "-" << prod->prodNum;
		break;
	}
	}
}

/* Snapshot every raw conflict (before precedence resolution) so the report can
 * still list conflicts that are later resolved or removed (e.g. by nonassoc).
 * Actions are copied because the transition may be removed. */
void Compiler::snapshotPdaConflicts( PdaGraph *pdaGraph )
{
	pdaConflicts.empty();

	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		for ( TransMap::Iter tr = state->transMap; tr.lte(); tr++ ) {
			PdaTrans *trans = tr->value;
			int cls = pdaConflictClass( trans );
			if ( cls == 0 )
				continue;

			PdaConflictRec rec;
			rec.state = &*state;
			rec.lowKey = trans->lowKey;
			rec.kind = cls;
			rec.toStateNum = trans->toState != 0 ?
					trans->toState->stateNum : -1;
			for ( ActDataList::Iter act = trans->actions; act.lte(); act++ )
				rec.actions.append( *act );

			trans->conflictRec = pdaConflicts.length();
			pdaConflicts.append( rec );
		}
	}
}

/* Finalize the record for one transition once precedence resolution is done
 * with it. Called while the transition is still alive. */
void Compiler::finishPdaConflict( PdaTrans *trans )
{
	if ( trans->conflictRec < 0 )
		return;

	PdaConflictRec &rec = pdaConflicts[trans->conflictRec];
	rec.resolve = trans->conflictResolve;
	rec.stillConflict = ( pdaConflictClass( trans ) != 0 );

	if ( rec.stillConflict )
		rec.levelOnlyTie = pdaConflictLevelTie( trans );

	rec.survivingAction = trans->actions.length() > 0 ?
			trans->actions[0] : -1;
}

/* True if a surviving conflict holds only because two competing actions were
 * declared at the same precedence level with no associativity. */
bool Compiler::pdaConflictLevelTie( PdaTrans *trans )
{
	for ( int i = 0; i < trans->actions.length(); i++ ) {
		LangEl *li = predOf( trans, trans->actions[i] );
		if ( li == 0 || li->predType == PredNone )
			continue;

		for ( int j = i+1; j < trans->actions.length(); j++ ) {
			LangEl *lj = predOf( trans, trans->actions[j] );
			if ( lj == 0 || lj->predType == PredNone )
				continue;

			if ( li->predValue == lj->predValue )
				return true;
		}
	}
	return false;
}

/* JSON string escaping for identifiers, file names and token literals. */
static void jsonStr( std::ostream &out, const char *s )
{
	out << '"';
	for ( const char *p = s; p != 0 && *p != 0; p++ ) {
		switch ( *p ) {
		case '"':  out << "\\\""; break;
		case '\\': out << "\\\\"; break;
		case '\n': out << "\\n"; break;
		case '\r': out << "\\r"; break;
		case '\t': out << "\\t"; break;
		default:    out << *p; break;
		}
	}
	out << '"';
}

/* Write one action as a JSON object. */
static void jsonAction( std::ostream &out, Production **prodIdIndex,
		long act, long toStateNum )
{
	out << "{";
	switch ( act & SHIFT_REDUCE_MASK ) {
	case SHIFT_CODE:
		out << "\"type\":\"shift\",\"target\":" << toStateNum;
		break;

	case REDUCE_CODE:
	case SHIFT_REDUCE_CODE: {
		Production *prod = prodIdIndex[GET_SHIFT_REDUCE(act)];
		out << "\"type\":\""
			<< ( ( act & SHIFT_REDUCE_MASK ) == REDUCE_CODE ? "reduce" : "shift-reduce" )
			<< "\",\"production\":";
		jsonStr( out, prod->prodName->name );
		out << ",\"prodNum\":" << prod->prodNum;
		if ( prod->loc.fileName != 0 ) {
			out << ",\"file\":";
			jsonStr( out, locFileName( prod->loc ) );
			out << ",\"line\":" << prod->loc.line;
		}
		break;
	}
	}
	out << "}";
}

/* True if a record should be listed given the --pda-report=state/token
 * filters. The summary counts are unaffected; only listing is filtered. */
bool Compiler::pdaConflictPassesFilter( PdaState *state, long lowKey )
{
	if ( pdaReportFilterState >= 0 && state->stateNum != pdaReportFilterState )
		return false;

	if ( pdaReportFilterToken != 0 && *pdaReportFilterToken != 0 ) {
		LangEl *lel = langElIndex[lowKey];
		if ( lel == 0 || lel->lit == 0 )
			return false;
		if ( strcmp( lel->lit, pdaReportFilterToken ) != 0 )
			return false;
	}

	return true;
}

/* Print the competing items for one conflict identity. Reduce items are
 * token-independent; the shift candidate is printed for the representative
 * lookahead. */
void Compiler::printPdaConflictItems( std::ostream &out, PdaState *state,
		const PdaConflictRec &rec )
{
	for ( long k = 0; k < rec.actions.length(); k++ ) {
		long act = rec.actions[k];
		if ( ( act & SHIFT_REDUCE_MASK ) != REDUCE_CODE )
			continue;

		Production *target = prodIdIndex[GET_SHIFT_REDUCE(act)];
		int targetLength = prodLength( target );

		for ( DotSet::Iter dot = state->dotSet; dot.lte(); dot++ ) {
			if ( prodForDot( *dot ) != target )
				continue;
			if ( dotPosForDot( *dot ) == targetLength )
				printDotItemForConflict( out, *dot, "reduce" );
		}
	}

	if ( rec.kind != 1 )
		return;

	LangEl *lel = langElIndex[rec.lowKey];
	if ( lel == 0 )
		return;

	for ( DotSet::Iter dot = state->dotSet; dot.lte(); dot++ ) {
		Production *prod = prodForDot( *dot );
		if ( prod == 0 )
			continue;

		int dotPos = dotPosForDot( *dot );
		int pos = 0;
		for ( ProdElList::Iter el = *prod->prodElList; el.lte(); el++, pos++ ) {
			if ( pos == dotPos && el->langEl == lel ) {
				printDotItemForConflict( out, *dot, "shift" );
				break;
			}
		}
	}
}

/* The conflict report proper. Groups identical conflicts (same state, kind and
 * action set) so a single item-pair is printed once with its whole lookahead
 * set, instead of once per token. Covers ALL raw conflicts, annotated with how
 * precedence resolution disposed of them. */
void Compiler::printPdaConflicts( std::ostream &out, bool withItems, bool withShapes )
{
	long srRaw = 0, rrRaw = 0, srRem = 0, rrRem = 0;
	for ( long i = 0; i < pdaConflicts.length(); i++ ) {
		const PdaConflictRec &rec = pdaConflicts[i];
		if ( rec.kind == 1 ) {
			srRaw++;
			if ( rec.stillConflict ) srRem++;
		}
		else {
			rrRaw++;
			if ( rec.stillConflict ) rrRem++;
		}
	}

	out << "\n=== CONFLICTS (raw: " << srRaw << " shift/reduce, " << rrRaw
		<< " reduce/reduce; remaining: " << srRem << " shift/reduce, "
		<< rrRem << " reduce/reduce)";
	if ( pdaReportFilterState >= 0 )
		out << " [filter: state " << pdaReportFilterState << "]";
	if ( pdaReportFilterToken != 0 && *pdaReportFilterToken != 0 )
		out << " [filter: token " << pdaReportFilterToken << "]";
	out << " ===\n";

	/* Mark filtered-out records as used so grouping skips them. Summary
	 * counts above stay global. */
	Vector<char> used;
	for ( long i = 0; i < pdaConflicts.length(); i++ )
		used.append( pdaConflictPassesFilter( pdaConflicts[i].state,
				pdaConflicts[i].lowKey ) ? 0 : 1 );

	for ( long i = 0; i < pdaConflicts.length(); i++ ) {
		if ( used[i] )
			continue;

		const PdaConflictRec &r = pdaConflicts[i];
		Vector<long> group;

		for ( long j = i; j < pdaConflicts.length(); j++ ) {
			if ( used[j] )
				continue;

			const PdaConflictRec &s = pdaConflicts[j];
			if ( s.state != r.state || s.kind != r.kind ||
					s.toStateNum != r.toStateNum ||
					s.actions.length() != r.actions.length() )
				continue;

			bool same = true;
			for ( long k = 0; k < r.actions.length(); k++ ) {
				if ( s.actions[k] != r.actions[k] ) {
					same = false;
					break;
				}
			}
			if ( !same )
				continue;

			used[j] = 1;
			group.append( j );
		}

		/* Aggregate status across the group. */
		bool still = false, tie = false, nonassoc = false;
		bool byLevel = false, byAssoc = false;
		for ( long g = 0; g < group.length(); g++ ) {
			const PdaConflictRec &s = pdaConflicts[group[g]];
			still = still || s.stillConflict;
			tie = tie || s.levelOnlyTie;
			nonassoc = nonassoc || ( ( s.resolve & PdaResNonassoc ) != 0 );
			byLevel = byLevel || ( ( s.resolve & PdaResLevel ) != 0 );
			byAssoc = byAssoc || ( ( s.resolve & PdaResAssoc ) != 0 );
		}

		out << "\nstate " << r.state->stateNum << "  "
			<< ( r.kind == 1 ? "shift/reduce" : "reduce/reduce" ) << "  ";

		for ( long k = 0; k < r.actions.length(); k++ ) {
			if ( k != 0 )
				out << " | ";
			printPdaAction( out, r.actions[k], r.toStateNum );
		}

		out << "  [";
		if ( still && tie )
			out << "UNRESOLVED level-only tie";
		else if ( still )
			out << "UNRESOLVED no precedence";
		else if ( nonassoc && !byLevel && !byAssoc )
			out << "error nonassoc";
		else {
			out << "resolved";
			if ( byLevel )
				out << " by level";
			if ( byAssoc )
				out << " by assoc";
			if ( nonassoc )
				out << " + nonassoc error";
		}
		out << "]";

		/* Actions are stored in priority/ordinal order and the runtime
		 * indexes from the front, falling back to the next on a retry. So the
		 * first surviving action is the one attempted first. */
		long firstTry = -1;
		for ( long g = 0; g < group.length(); g++ ) {
			if ( pdaConflicts[group[g]].survivingAction >= 0 ) {
				firstTry = pdaConflicts[group[g]].survivingAction;
				break;
			}
		}
		if ( still && firstTry >= 0 ) {
			out << " (runtime first-tries ";
			printPdaAction( out, firstTry, r.toStateNum );
			out << ", then retries)";
		}

		out << "\ntokens(" << group.length() << "):";
		for ( long g = 0; g < group.length(); g++ ) {
			const PdaConflictRec &s = pdaConflicts[group[g]];
			LangEl *lel = langElIndex[s.lowKey];
			if ( lel != 0 )
				out << " " << lel->lit;
			else
				out << " <" << s.lowKey << ">";
		}
		out << "\n";

		if ( withItems )
			printPdaConflictItems( out, r.state, r );
	}

	if ( withShapes )
		printPdaConflictShapes( out );

	out << "\n";
}

/* Canonical order for an action set. The stored order is the runtime
 * first-try order, which is not meaningful to a shape, so sorting it lets
 * shapes that differ only in that order aggregate together. */
static void sortActionCodes( Vector<long> &actions )
{
	for ( long i = 1; i < actions.length(); i++ ) {
		long v = actions[i];
		long j = i - 1;
		while ( j >= 0 && actions[j] > v ) {
			actions[j + 1] = actions[j];
			j--;
		}
		actions[j + 1] = v;
	}
}

/* Aggregate identical conflict identities across states: an author fixes a
 * shape, not a state. Only shapes spanning more than one state are shown,
 * since single-state shapes are already listed above. */
void Compiler::printPdaConflictShapes( std::ostream &out )
{
	struct Shape {
		int kind;
		long toStateNum;
		Vector<long> actions;
		Vector<long> states;
		bool still;
	};
	Vector<Shape> shapes;

	Vector<char> used;
	for ( long i = 0; i < pdaConflicts.length(); i++ )
		used.append( pdaConflictPassesFilter( pdaConflicts[i].state,
				pdaConflicts[i].lowKey ) ? 0 : 1 );

	for ( long i = 0; i < pdaConflicts.length(); i++ ) {
		if ( used[i] )
			continue;

		const PdaConflictRec &r = pdaConflicts[i];
		Shape sh;
		sh.kind = r.kind;
		sh.toStateNum = r.toStateNum;
		sh.still = false;
		for ( long k = 0; k < r.actions.length(); k++ )
			sh.actions.append( r.actions[k] );
		sortActionCodes( sh.actions );

		for ( long j = i; j < pdaConflicts.length(); j++ ) {
			if ( used[j] )
				continue;

			const PdaConflictRec &s = pdaConflicts[j];
			if ( s.kind != r.kind || s.toStateNum != r.toStateNum ||
					s.actions.length() != r.actions.length() )
				continue;

			Vector<long> sActions;
			for ( long k = 0; k < s.actions.length(); k++ )
				sActions.append( s.actions[k] );
			sortActionCodes( sActions );

			bool same = true;
			for ( long k = 0; k < r.actions.length(); k++ ) {
				if ( sActions[k] != sh.actions[k] ) {
					same = false;
					break;
				}
			}
			if ( !same )
				continue;

			used[j] = 1;

			bool seen = false;
			for ( long q = 0; q < sh.states.length(); q++ ) {
				if ( sh.states[q] == s.state->stateNum ) {
					seen = true;
					break;
				}
			}
			if ( !seen )
				sh.states.append( s.state->stateNum );

			sh.still = sh.still || s.stillConflict;
		}

		shapes.append( sh );
	}

	bool anyMulti = false;
	for ( long i = 0; i < shapes.length(); i++ ) {
		if ( shapes[i].states.length() > 1 ) {
			anyMulti = true;
			break;
		}
	}
	if ( !anyMulti )
		return;

	out << "\n=== CONFLICT SHAPES (same action set across states) ===\n";

	for ( long i = 0; i < shapes.length(); i++ ) {
		Shape &sh = shapes[i];
		if ( sh.states.length() < 2 )
			continue;

		out << "  " << ( sh.kind == 1 ? "shift/reduce " : "reduce/reduce" )
			<< "  ";
		for ( long k = 0; k < sh.actions.length(); k++ ) {
			if ( k != 0 )
				out << " | ";
			printPdaAction( out, sh.actions[k], sh.toStateNum );
		}
		out << "  [" << sh.states.length() << " states] (states";
		for ( long q = 0; q < sh.states.length(); q++ )
			out << " " << sh.states[q];
		out << ")" << ( sh.still ? " UNRESOLVED" : "" ) << "\n";
	}
}

/* JSON form of the grouped conflicts, plus the cross-state shapes. Stable key
 * order so CI can diff two revisions. Locations are included when known. */
void Compiler::printPdaConflictsJson( std::ostream &out )
{
	long srRaw = 0, rrRaw = 0, srRem = 0, rrRem = 0;
	for ( long i = 0; i < pdaConflicts.length(); i++ ) {
		const PdaConflictRec &rec = pdaConflicts[i];
		if ( rec.kind == 1 ) {
			srRaw++;
			if ( rec.stillConflict ) srRem++;
		}
		else {
			rrRaw++;
			if ( rec.stillConflict ) rrRem++;
		}
	}

	out << "{\n";
	out << "  \"rawShiftReduce\": " << srRaw << ",\n";
	out << "  \"rawReduceReduce\": " << rrRaw << ",\n";
	out << "  \"remainingShiftReduce\": " << srRem << ",\n";
	out << "  \"remainingReduceReduce\": " << rrRem << ",\n";
	if ( pdaReportFilterState >= 0 )
		out << "  \"filterState\": " << pdaReportFilterState << ",\n";
	if ( pdaReportFilterToken != 0 && *pdaReportFilterToken != 0 ) {
		out << "  \"filterToken\": ";
		jsonStr( out, pdaReportFilterToken );
		out << ",\n";
	}

	Vector<char> used;
	for ( long i = 0; i < pdaConflicts.length(); i++ )
		used.append( pdaConflictPassesFilter( pdaConflicts[i].state,
				pdaConflicts[i].lowKey ) ? 0 : 1 );

	out << "  \"conflicts\": [";
	bool firstGroup = true;

	for ( long i = 0; i < pdaConflicts.length(); i++ ) {
		if ( used[i] )
			continue;

		const PdaConflictRec &r = pdaConflicts[i];
		Vector<long> group;

		for ( long j = i; j < pdaConflicts.length(); j++ ) {
			if ( used[j] )
				continue;

			const PdaConflictRec &s = pdaConflicts[j];
			if ( s.state != r.state || s.kind != r.kind ||
					s.toStateNum != r.toStateNum ||
					s.actions.length() != r.actions.length() )
				continue;

			bool same = true;
			for ( long k = 0; k < r.actions.length(); k++ ) {
				if ( s.actions[k] != r.actions[k] ) {
					same = false;
					break;
				}
			}
			if ( !same )
				continue;

			used[j] = 1;
			group.append( j );
		}

		bool still = false, tie = false, nonassoc = false;
		bool byLevel = false, byAssoc = false;
		for ( long g = 0; g < group.length(); g++ ) {
			const PdaConflictRec &s = pdaConflicts[group[g]];
			still = still || s.stillConflict;
			tie = tie || s.levelOnlyTie;
			nonassoc = nonassoc || ( ( s.resolve & PdaResNonassoc ) != 0 );
			byLevel = byLevel || ( ( s.resolve & PdaResLevel ) != 0 );
			byAssoc = byAssoc || ( ( s.resolve & PdaResAssoc ) != 0 );
		}

		if ( !firstGroup )
			out << ",";
		firstGroup = false;

		out << "\n    {\"state\": " << r.state->stateNum << ", ";
		out << "\"kind\": ";
		jsonStr( out, r.kind == 1 ? "shift/reduce" : "reduce/reduce" );

		out << ", \"status\": ";
		if ( still )
			out << "\"unresolved\"";
		else if ( nonassoc && !byLevel && !byAssoc )
			out << "\"nonassoc-error\"";
		else
			out << "\"resolved\"";

		if ( still )
			out << ", \"tie\": " << ( tie ? "true" : "false" );
		else if ( byLevel || byAssoc ) {
			out << ", \"resolvedBy\": \"";
			bool plus = false;
			if ( byLevel ) { out << "level"; plus = true; }
			if ( byAssoc ) { if ( plus ) out << "+"; out << "assoc"; }
			out << "\"";
		}

		out << ", \"actions\": [";
		for ( long k = 0; k < r.actions.length(); k++ ) {
			if ( k != 0 )
				out << ", ";
			jsonAction( out, prodIdIndex, r.actions[k], r.toStateNum );
		}
		out << "]";

		long firstTry = -1;
		for ( long g = 0; g < group.length(); g++ ) {
			if ( pdaConflicts[group[g]].survivingAction >= 0 ) {
				firstTry = pdaConflicts[group[g]].survivingAction;
				break;
			}
		}
		out << ", \"runtimeFirst\": ";
		if ( still && firstTry >= 0 )
			jsonAction( out, prodIdIndex, firstTry, r.toStateNum );
		else
			out << "null";

		out << ", \"tokens\": [";
		for ( long g = 0; g < group.length(); g++ ) {
			if ( g != 0 )
				out << ", ";
			const PdaConflictRec &s = pdaConflicts[group[g]];
			LangEl *lel = langElIndex[s.lowKey];
			if ( lel != 0 && lel->lit != 0 )
				jsonStr( out, lel->lit );
			else {
				char buf[32];
				snprintf( buf, sizeof(buf), "<%ld>", s.lowKey );
				jsonStr( out, buf );
			}
		}
		out << "]}";
	}

	out << "\n  ],\n";

	/* Cross-state shapes. */
	for ( long i = 0; i < pdaConflicts.length(); i++ )
		used[i] = pdaConflictPassesFilter( pdaConflicts[i].state,
				pdaConflicts[i].lowKey ) ? 0 : 1;

	out << "  \"shapes\": [";
	bool firstShape = true;

	for ( long i = 0; i < pdaConflicts.length(); i++ ) {
		if ( used[i] )
			continue;

		const PdaConflictRec &r = pdaConflicts[i];
		Vector<long> rActions;
		for ( long k = 0; k < r.actions.length(); k++ )
			rActions.append( r.actions[k] );
		sortActionCodes( rActions );
		Vector<long> states;
		bool still = false;

		for ( long j = i; j < pdaConflicts.length(); j++ ) {
			if ( used[j] )
				continue;

			const PdaConflictRec &s = pdaConflicts[j];
			if ( s.kind != r.kind || s.toStateNum != r.toStateNum ||
					s.actions.length() != r.actions.length() )
				continue;

			Vector<long> sActions;
			for ( long k = 0; k < s.actions.length(); k++ )
				sActions.append( s.actions[k] );
			sortActionCodes( sActions );

			bool same = true;
			for ( long k = 0; k < rActions.length(); k++ ) {
				if ( sActions[k] != rActions[k] ) {
					same = false;
					break;
				}
			}
			if ( !same )
				continue;

			used[j] = 1;

			bool seen = false;
			for ( long q = 0; q < states.length(); q++ ) {
				if ( states[q] == s.state->stateNum ) {
					seen = true;
					break;
				}
			}
			if ( !seen )
				states.append( s.state->stateNum );

			still = still || s.stillConflict;
		}

		if ( states.length() < 2 )
			continue;

		if ( !firstShape )
			out << ",";
		firstShape = false;

		out << "\n    {\"kind\": ";
		jsonStr( out, r.kind == 1 ? "shift/reduce" : "reduce/reduce" );
		out << ", \"actions\": [";
		for ( long k = 0; k < rActions.length(); k++ ) {
			if ( k != 0 )
				out << ", ";
			jsonAction( out, prodIdIndex, rActions[k], r.toStateNum );
		}
		out << "], \"states\": [";
		for ( long q = 0; q < states.length(); q++ ) {
			if ( q != 0 )
				out << ", ";
			out << states[q];
		}
		out << "], \"unresolved\": " << ( still ? "true" : "false" ) << "}";
	}

	out << "\n  ]\n}\n";
}

void Compiler::printPdaState( std::ostream &out, PdaState *state )
{
	out << "\nstate " << state->stateNum;
	printPdaStateConflicts( out, state );
	out << "\n\n";

	/* Print LR items. */
	for ( DotSet::Iter dot = state->dotSet; dot.lte(); dot++ )
		printDotItem( out, *dot );

	out << "\n";

	/* Print finalized transitions and actions. */
	for ( TransMap::Iter tr = state->transMap; tr.lte(); tr++ ) {
		PdaTrans *trans = tr->value;
		LangEl *lel = langElIndex[trans->lowKey];

		out << "    ";

		if ( lel != 0 )
			out << lel->lit;
		else
			out << "<" << trans->lowKey << ">";

		if ( trans->actions.length() == 0 ) {
			out << "  (no actions)\n";
			continue;
		}

		for ( ActDataList::Iter act = trans->actions; act.lte(); act++ ) {
			switch ( *act & SHIFT_REDUCE_MASK ) {
			case SHIFT_CODE:
				out << "  shift " << trans->toState->stateNum;
				break;

			case REDUCE_CODE: {
				Production *prod = prodIdIndex[GET_SHIFT_REDUCE(*act)];
				out << "  reduce "
					 << prod->prodName->name << "-"
					 << prod->prodNum;
				break;
			}

			case SHIFT_REDUCE_CODE: {
				Production *prod = prodIdIndex[GET_SHIFT_REDUCE(*act)];
				out << "  shift-reduce "
					 << prod->prodName->name << "-"
					 << prod->prodNum;
				break;
			}
			}

			if ( !act.last() )
				out << " |";
		}

		out << "\n";
		printConflictDetails( out, state, trans );
	}
}

void Compiler::printPdaStateConflicts( std::ostream &out, PdaState *state )
{
	int shiftReduceTransitions = 0;
	int reduceReduceTransitions = 0;
	int shiftReducePairs = 0;
	int reduceReducePairs = 0;

	for ( TransMap::Iter tr = state->transMap;
		  tr.lte(); tr++ )
	{
		PdaTrans *trans = tr->value;

		int shifts = 0;
		int reductions = 0;

		for ( ActDataList::Iter act = trans->actions;
			  act.lte(); act++ )
		{
			switch ( *act & SHIFT_REDUCE_MASK ) {
			case SHIFT_CODE:
				shifts++;
				break;

			case REDUCE_CODE:
				reductions++;
				break;

			case SHIFT_REDUCE_CODE:
				break;
			}
		}

		if ( shifts > 0 && reductions > 0 )
			shiftReduceTransitions++;

		if ( reductions > 1 )
			reduceReduceTransitions++;

		shiftReducePairs += shifts * reductions;
		reduceReducePairs += reductions * ( reductions - 1 ) / 2;
	}

	out << "  ["
		 << shiftReduceTransitions << " shift/reduce transitions, "
		 << reduceReduceTransitions << " reduce/reduce transitions; "
		 << shiftReducePairs << " shift/reduce pairs, "
		 << reduceReducePairs << " reduce/reduce pairs]\n";
}

void Compiler::printPdaReport( std::ostream &out, PdaGraph *pdaGraph, bool conflictsOnly )
{
	for ( PdaStateList::Iter state = pdaGraph->stateList;
		  state.lte(); state++ )
	{
		if ( conflictsOnly && !pdaStateHasConflict( &*state ) )
			continue;
		printPdaState( out, &*state );
	}
}

void Compiler::printDotItem( std::ostream &out, long dot )
{
    Production *prod = prodForDot( dot );
	if ( prod == 0 ) {
		out << "    <unknown dot " << dot << ">\n";
		return;
	}

	int dotPos = dotPosForDot( dot );

	out << "    " << prod->prodName->name << " -> ";

	int pos = 0;

	for ( ProdElList::Iter el = *prod->prodElList;
		  el.lte(); el++, pos++ )
	{
		if ( pos == dotPos )
			out << ". ";

		if ( el->langEl != 0 )
			out << el->langEl->lit;
		else
			out << "?";

		out << " ";
	}

	if ( pos == dotPos )
		out << ".";

	printLocSuffix( out, prod );

	out << "\n";
}

/* Assign state numbers for the report in a deterministic order: breadth-first
 * from the start state, following transitions in token-key order (transMap is
 * ordered, stateList is not stable across runs). This keeps report output
 * byte-stable and makes the raw dump and the conflict index agree. Code
 * generation still uses PdaGraph::setStateNumbers; this is report-only. */
void Compiler::assignReportStateNumbers( PdaGraph *pdaGraph )
{
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ )
		state->stateNum = -1;

	Vector<PdaState*> queue;
	PdaState *start = pdaGraph->startState;
	if ( start != 0 ) {
		start->stateNum = 0;
		queue.append( start );
	}

	int next = 1;
	for ( int qi = 0; qi < queue.length(); qi++ ) {
		PdaState *state = queue[qi];
		for ( TransMap::Iter tel = state->transMap; tel.lte(); tel++ ) {
			PdaState *to = tel->value->toState;
			if ( to != 0 && to->stateNum < 0 ) {
				to->stateNum = next++;
				queue.append( to );
			}
		}
	}

	/* States unreachable from the start keep a stable tail number. */
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		if ( state->stateNum < 0 )
			state->stateNum = next++;
	}
}

void Compiler::printRawConflictReport( std::ostream &out, PdaGraph *pdaGraph )
{
	assignReportStateNumbers( pdaGraph );

	out << "\n=== RAW CONFLICT REPORT "
		 << "(before precedence resolution) ===\n";

	printPdaReport( out, pdaGraph, false );
}

void Compiler::printFinalConflictReport( std::ostream &out, PdaGraph *pdaGraph,
		bool conflictsOnly )
{
	assignReportStateNumbers( pdaGraph );

	out << "\n=== CONFLICT REPORT "
		 << "(after precedence resolution) ===\n";

	printPdaReport( out, pdaGraph, conflictsOnly );
}

void Compiler::sortActions( PdaGraph *pdaGraph )
{
	/* Sort the actions. */
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		assert( CmpDotSet::compare( state->dotSet, state->dotSet2 ) == 0 );
		for ( TransMap::Iter tel = state->transMap; tel.lte(); tel++ ) {
			PdaTrans *trans = tel->value;

			/* Sort by the action ords. */
			ActDataList actions( trans->actions );
			ActDataList actOrds( trans->actOrds );
			ActDataList actPriors( trans->actPriors );
			trans->actions.empty();
			trans->actOrds.empty();
			trans->actPriors.empty();
			while ( actOrds.length() > 0 ) {
				int min = 0;
				for ( int i = 1; i < actOrds.length(); i++ ) {
					if ( actPriors[i] > actPriors[min] ||
							(actPriors[i] == actPriors[min] &&
							actOrds[i] < actOrds[min] ) )
					{
						min = i;
					}
				}
				trans->actions.append( actions[min] );
				trans->actOrds.append( actOrds[min] );
				trans->actPriors.append( actPriors[min] );
				actions.remove(min);
				actOrds.remove(min);
				actPriors.remove(min);
			}

			if ( trans->actions.length() > 1 )
			    recordPdaConflict( trans );

			if ( branchPointInfo && trans->actions.length() > 1 ) {
				cerr << "RAW CONFLICT"
				    << " state: " << state->stateNum
				    << " trans: ";
				LangEl *lel = langElIndex[trans->lowKey];

				if ( lel == 0 )
				    cerr << (char)trans->lowKey << endl;
				else
				    cerr << lel->lit << endl;

				cerr << "    DOT ITEMS:" << endl;
				for ( DotSet::Iter dot = state->dotSet; dot.lte(); dot++ ) {
				    DotItemIndexEl *di = dotItemIndex.find(*dot);
				    cerr << "        dot=" << *dot;
				    if (di != 0) {
				        Production *prod = di->value;
				        cerr << " prodId=" << prod->prodId
				             << " prodNum=" << prod->prodNum
				             << " prodName=" << prod->prodName->name;
						printDotItem( cerr, *dot );
				    }
				    else {
				        cerr << " <NO PRODUCTION>";
				    }
				    cerr << endl;
				}

				for ( ActDataList::Iter act = trans->actions; act.lte(); act++ ) {
				    long action = *act;

				    switch ( action & SHIFT_REDUCE_MASK ) {
				    case SHIFT_CODE:
				        cerr << "    SHIFT"
				             << " action=" << action
				             << " target=" << trans->toState
				             << endl;
				        break;

				    case REDUCE_CODE:
					{
					    int prodId = GET_SHIFT_REDUCE(action);
					    Production *prod = prodIdIndex[prodId];

					    cerr << "    REDUCE "
					         << prod->data
					         << " prodId=" << prodId
					         << " action=" << action
					         << endl;

					    break;
					}

				    case SHIFT_REDUCE_CODE:
				        cerr << "    SHIFT-REDUCE"
				             << " action=" << action
				             << endl;
				        break;
				    }
				}

				cerr << "info: branch point"
						<< " state: " << state->stateNum
						<< " trans: ";
				lel = langElIndex[trans->lowKey];
				if ( lel == 0 )
					cerr << (char)trans->lowKey << endl;
				else
					cerr << lel->lit << endl;

				for ( ActDataList::Iter act = trans->actions; act.lte(); act++ ) {
					switch ( *act & SHIFT_REDUCE_MASK ) {
					case SHIFT_CODE:
						cerr << "    shift" << endl;
						break;
					case REDUCE_CODE:
						cerr << "    reduce " <<
								prodIdIndex[GET_SHIFT_REDUCE(*act)]->data << endl;
						break;
					case SHIFT_REDUCE_CODE:
						cerr << "    shift-reduce" << endl;
						break;
					}
				}
			}

			/* Verify that shifts of nonterminals don't have any branch
			 * points or commits. */
			if ( trans->lowKey >= firstNonTermId ) {
				if ( trans->actions.length() != 1 ||
					(trans->actions[0] & SHIFT_REDUCE_MASK) != 1 )
				{
					error() << "TRANS ON NONTERMINAL is something "
						"other than a shift" << endl;
				}
				if ( trans->commits.length() > 0 )
					error() << "TRANS ON NONTERMINAL has a commit" << endl;
			}

			/* TODO: Shift-reduces are optimizations. Verify that
			 * shift-reduces exist only if they don't entail a conflict. */
		}
	}
}

void Compiler::reduceActions( PdaGraph *pdaGraph )
{
	/* Reduce the actions. */
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		for ( TransMap::Iter tel = state->transMap; tel.lte(); tel++ ) {
			PdaTrans *trans = tel->value;
			PdaActionSetEl *inSet;

			int commitLen = trans->commits.length() > 0 ?
				trans->commits[trans->commits.length()-1] : 0;

			if ( trans->afterShiftCommits.length() > 0 ) {
				int afterShiftCommit = trans->afterShiftCommits[
					trans->afterShiftCommits.length()-1];

				if ( commitLen > 0 && commitLen+1 > afterShiftCommit )
					commitLen = ( commitLen + 1 );
				else
					commitLen = afterShiftCommit;
			}
			else {
				commitLen = commitLen * -1;
			}

			//if ( commitLen != 0 ) {
			//	cerr << "FINAL ACTION COMMIT LEN: " << commitLen << endl;
			//}

			pdaGraph->actionSet.insert( ActionData( trans->toState->stateNum,
					trans->actions, commitLen ), &inSet );
			trans->actionSetEl = inSet;
		}
	}
}

void Compiler::computeAdvanceReductions( LangEl *langEl, PdaGraph *pdaGraph )
{
	/* Get the entry into the graph and traverse over the root. The resulting
	 * state can have eof, nothing else can. */
	PdaState *overStart = pdaGraph->followFsm(
			langEl->startState,
			langEl->rootDef->fsm );

	/* The graph must reduce to root all on it's own. It cannot depend on
	 * require EOF. */
	for ( PdaStateList::Iter st = pdaGraph->stateList; st.lte(); st++ ) {
		if ( st == overStart )
			continue;

		for ( TransMap::Iter tr = st->transMap; tr.lte(); tr++ ) {
			if ( tr->value->lowKey == langEl->eofLel->id )
				st->advanceReductions = true;
		}
	}
}

void Compiler::verifyParseStopGrammar( LangEl *langEl, PdaGraph *pdaGraph )
{
	/* Get the entry into the graph and traverse over the root. The resulting
	 * state can have eof, nothing else can. */
	PdaState *overStart = pdaGraph->followFsm(
			langEl->startState,
			langEl->rootDef->fsm );

	/* The graph must reduce to root all on it's own. It cannot depend on
	 * require EOF. */
	for ( PdaStateList::Iter st = pdaGraph->stateList; st.lte(); st++ ) {
		if ( st == overStart )
			continue;

		for ( TransMap::Iter tr = st->transMap; tr.lte(); tr++ ) {
			if ( tr->value->lowKey == langEl->eofLel->id ) {
				/* This needs a better error message. Appears to be voodoo. */
				error() << "grammar is not usable with parse_stop" << endp;
			}
		}
	}
}

LangEl *Compiler::predOf( PdaTrans *trans, long action )
{
	LangEl *lel;
	if ( action == SHIFT_CODE )
		lel = langElIndex[trans->lowKey];
	else
		lel = prodIdIndex[GET_SHIFT_REDUCE(action)]->predOf;
	return lel;
}


PredOutcome Compiler::precedenceSwap( long action1, long action2, LangEl *l1, LangEl *l2 )
{
	/* Different levels: the higher level wins; associativity is irrelevant. */
	if ( l1->predValue != l2->predValue )
		return ( l2->predValue > l1->predValue ) ? PrecSwap : PrecKeep;

	/* Equal levels: bison consults the lookahead (shift) token's associativity. */
	LangEl *lShift = ( action1 == SHIFT_CODE ) ? l1 :
			( action2 == SHIFT_CODE ) ? l2 : 0;

	if ( lShift != 0 ) {
		switch ( lShift->predType ) {
		case PredLeft:
			/* left assoc -> reduce wins */
			return ( action1 == SHIFT_CODE ) ? PrecSwap : PrecKeep;

		case PredRight:
			/* right assoc -> shift wins */
			return ( action2 == SHIFT_CODE ) ? PrecSwap : PrecKeep;

		case PredNonassoc:
			/* neither action survives */
			return PrecNonassoc;

		case PredPrecedence:
			/* Level only, no associativity to decide with. Leave it as a
			 * visible conflict. */
			return PrecUndecided;

		default:
			break;
		}
	}

	/* Reduce/reduce (no shift token). Keep the historical behavior, but make
	 * level-only ties visible. */
	if ( l1->predType == PredNonassoc )
		return PrecNonassoc;
	if ( l1->predType == PredPrecedence || l2->predType == PredPrecedence )
		return PrecUndecided;
	return PrecKeep;
}

/* Emit a per-conflict line for the --pda-report output. */
void Compiler::printPrecedenceDecision( std::ostream &out, PdaState *state,
		PdaTrans *trans, LangEl *l1, LangEl *l2, PredOutcome result )
{
	LangEl *tok = langElIndex[trans->lowKey];

	out << "precedence: state " << state->stateNum << " token ";
	if ( tok != 0 )
		out << tok->lit;
	else
		out << "<" << trans->lowKey << ">";

	out << " (l1 " << l1->predValue << ", l2 " << l2->predValue << ") -> ";
	switch ( result ) {
	case PrecSwap:      out << "swap"; break;
	case PrecKeep:      out << "keep"; break;
	case PrecNonassoc:  out << "nonassoc (error)"; break;
	case PrecUndecided: out << "undecided (level-only tie)"; break;
	}
	out << "\n";
}

void Compiler::resolvePrecedence( PdaGraph *pdaGraph, std::ostream &report )
{
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		assert( CmpDotSet::compare( state->dotSet, state->dotSet2 ) == 0 );

		for ( long t = 0; t < state->transMap.length(); /* increment at end */ ) {
			PdaTrans *trans = state->transMap[t].value;

again:
			/* Find action with precedence. */
			for ( int i = 0; i < trans->actions.length(); i++ ) {
				LangEl *li = predOf( trans, trans->actions[i] );

				if ( li != 0 && li->predType != PredNone ) {
					/* Find another action with precedence. */
					for ( int j = i+1; j < trans->actions.length(); j++ ) {
						LangEl *lj = predOf( trans, trans->actions[j] );

						if ( lj != 0 && lj->predType != PredNone ) {
							/* Conflict to check. */
							PredOutcome out = precedenceSwap( trans->actions[i],
									trans->actions[j], li, lj );

							if ( out == PrecUndecided ) {
								/* Level-only precedence: there is no associativity
								 * to decide with. Leave both actions; the conflict
								 * stays and is counted in "remaining". Do not goto
								 * again: this scan only terminates by removing an
								 * action. */
								pdaPrecedenceTies++;
								if ( generatePdaReport && pdaReportMode == PdaReportFull )
									printPrecedenceDecision( report, state, trans, li, lj, out );
								continue;
							}

							bool byLevel = ( li->predValue != lj->predValue );

							if ( out == PrecSwap ) {
								long tmpAct = trans->actions[i];
								trans->actions[i] = trans->actions[j];
								trans->actions[j] = tmpAct;
							}

							if ( out == PrecNonassoc ) {
								pdaResolvedNonassoc++;
								trans->conflictResolve |= PdaResNonassoc;
							}
							else if ( byLevel ) {
								pdaResolvedByLevel++;
								trans->conflictResolve |= PdaResLevel;
							}
							else {
								pdaResolvedByAssoc++;
								trans->conflictResolve |= PdaResAssoc;
							}

							if ( generatePdaReport && pdaReportMode == PdaReportFull )
								printPrecedenceDecision( report, state, trans, li, lj, out );

							trans->actions.remove( j );
							if ( out == PrecNonassoc )
								trans->actions.remove( i );

							goto again;
						}
					}
				}
			}

			/* If there are still actions then move to the next one. If not,
			 * (due to nonassoc) then remove the transition. Either way the record
			 * can be finalized now, while the transition is still alive. */
			finishPdaConflict( trans );

			if ( trans->actions.length() > 0 )
				t += 1;
			else
				state->transMap.vremove( t );
		}
	}
}

void Compiler::analyzeMachine( PdaGraph *pdaGraph, LangElSet &parserEls )
{
	pdaGraph->maxState = pdaGraph->stateList.length() - 1;
	pdaGraph->maxLelId = nextLelId - 1;
	pdaGraph->maxOffset = pdaGraph->stateList.length() * pdaGraph->maxLelId;

	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		for ( TransMap::Iter trans = state->transMap; trans.lte(); trans++ ) {
			if ( trans->value->isShift ) {
				trans->value->actions.append( SHIFT_CODE );
				trans->value->actPriors.append( trans->value->shiftPrior );
			}
			for ( ReductionMap::Iter red = trans->value->reductions; red.lte(); red++ ) {
				trans->value->actions.append( makeReduceCode( red->key, false ) );
				trans->value->actPriors.append( red->value );
			}
			trans->value->actOrds.appendDup( 0, trans->value->actions.length() );
		}
	}

	pdaActionOrder( pdaGraph, parserEls );
	sortActions( pdaGraph );

	/* Conflict sites (distinct state + kind + shift target + action set),
	 * counted before precedence resolution so the summary can distinguish the
	 * number of decisions from the per-lookahead pair counts. */
	long conflictEntries = countPdaConflictEntries( pdaGraph );

	/* All report output goes to one stream so it can be redirected as a unit. */
	std::ostream &report = pdaReportStream != 0 ? *pdaReportStream : cerr;

	/* Capture every raw conflict before resolution touches the transitions, so
	 * the report can show what happened to each one. Needs state numbers. */
	if ( generatePdaReport ) {
		assignReportStateNumbers( pdaGraph );
		snapshotPdaConflicts( pdaGraph );
	}

	if ( generatePdaReport && pdaReportMode == PdaReportFull )
		printRawConflictReport( report, pdaGraph );

	resolvePrecedence( pdaGraph, report );

	if ( generatePdaReport ) {
		if ( pdaReportMode == PdaReportJson ) {
			printPdaConflictsJson( report );
		}
		else {
			printPdaConflicts( report,
					pdaReportMode == PdaReportConflicts,
					pdaReportMode == PdaReportClusters );
			if ( pdaReportMode == PdaReportFull )
				printFinalConflictReport( report, pdaGraph, false );
		}
	}

	/* Recount the conflicts that survived precedence resolution. This is the
	 * authoritative "remaining" figure; the per-pair counters above are
	 * diagnostics and can double-count a multi-action conflict site. */
	countPdaConflicts( pdaGraph, pdaRemainingShiftReduce, pdaRemainingReduceReduce );
	pdaResolvedConflicts = ( pdaShiftReduceConflicts - pdaRemainingShiftReduce ) +
			( pdaReduceReduceConflicts - pdaRemainingReduceReduce );

	/* Verify that any type we parse_stop can actually be parsed that way. */
	for ( LangElSet::Iter pe = parserEls; pe.lte(); pe++ ) {
		LangEl *lel = *pe;
		if ( lel->parseStop )
			computeAdvanceReductions(lel , pdaGraph);
	}

	advanceReductions( pdaGraph );
	pdaGraph->setStateNumbers();

	if ( generatePdaReport && pdaReportMode == PdaReportFull ) {
		report << "\n=== PDA AFTER ADVANCE REDUCTIONS ===\n";
		printPdaReport( report, pdaGraph, false );
	}

	reduceActions( pdaGraph );

	if ( generatePdaReport && pdaReportMode == PdaReportFull ) {
		report << "\n=== PDA AFTER ACTION REDUCTION ===\n";
		printPdaReport( report, pdaGraph, false );
	}

	/* Set the action ids. */
	int actionSetId = 0;
	for ( PdaActionSet::Iter asi = pdaGraph->actionSet; asi.lte(); asi++ )
		asi->key.id = actionSetId++;

	/* Get the max index. */
	pdaGraph->maxIndex = actionSetId - 1;

	/* Compute the max prod length. */
	pdaGraph->maxProdLen = 0;
	for ( ProdList::Iter prod = prodList; prod.lte(); prod++ ) {
		if ( (unsigned)prod->fsmLength > pdaGraph->maxProdLen )
			pdaGraph->maxProdLen = prod->fsmLength;
	}

	/* Asserts that any transition with a nonterminal has a single action
	 * which is either a shift or a shift-reduce. */
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		for ( TransMap::Iter trans = state->transMap; trans.lte(); trans++ ) {
			LangEl *langEl = langElIndex[trans->value->lowKey];
			if ( langEl != 0 && langEl->type == LangEl::NonTerm ) {
				assert( trans->value->actions.length() == 1 );
				assert( trans->value->actions[0] == SHIFT_CODE ||
					(trans->value->actions[0] & SHIFT_REDUCE_MASK) == SHIFT_REDUCE_CODE );
			}
		}
	}

	/* Assert that shift reduces always appear on their own. */
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		for ( TransMap::Iter trans = state->transMap; trans.lte(); trans++ ) {
			for ( ActDataList::Iter act = trans->value->actions; act.lte(); act++ ) {
				if ( (*act & SHIFT_REDUCE_MASK) == SHIFT_REDUCE_CODE )
					assert( trans->value->actions.length() == 1 );
			}
		}
	}

	/* Verify that any type we parse_stop can actually be parsed that way. */
	for ( LangElSet::Iter pe = parserEls; pe.lte(); pe++ ) {
		LangEl *lel = *pe;
		if ( lel->parseStop )
			verifyParseStopGrammar(lel , pdaGraph);
	}

	long unresolved = pdaRemainingShiftReduce + pdaRemainingReduceReduce;
	/* In JSON mode the report stream must contain JSON only. */
	if ( pdaReportMode != PdaReportJson ) {
		cerr << "conflicts: "
			<< pdaShiftReduceConflicts << " shift/reduce, "
			<< pdaReduceReduceConflicts << " reduce/reduce over "
			<< conflictEntries << " conflict entries, "
			<< pdaResolvedConflicts << " resolved ("
			<< pdaResolvedByLevel << " by level, "
			<< pdaResolvedByAssoc << " by assoc, "
			<< pdaResolvedNonassoc << " nonassoc->error), "
			<< pdaPrecedenceTies << " level-only ties, "
			<< unresolved << " remaining ("
			<< pdaRemainingShiftReduce << " shift/reduce, "
			<< pdaRemainingReduceReduce << " reduce/reduce)"
			<< endl;
	}
}

void Compiler::wrapNonTerminals()
{
	/* Make a language element that will be used to make the root productions.
	 * These are used for making parsers rooted at any production (including
	 * the start symbol). */
	rootLangEl = declareLangEl( this, rootNamespace, "_root", LangEl::NonTerm );

	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		/* Make a single production used when the lel is a root. */
		ProdElList *prodElList = makeProdElList( lel );
		lel->rootDef = Production::cons( InputLoc(), rootLangEl,
				prodElList, String(), false, 0,
				prodList.length(), rootLangEl->prodList.length() );
		prodList.append( lel->rootDef );
		rootLangEl->prodList.append( lel->rootDef );

		/* First resolve. */
		for ( ProdElList::Iter prodEl = *prodElList; prodEl.lte(); prodEl++ )
			resolveProdEl( prodEl );
	}
}

bool Compiler::makeNonTermFirstSetProd( Production *prod, PdaState *state )
{
	bool modified = false;
	for ( TransMap::Iter trans = state->transMap; trans.lte(); trans++ ) {
		if ( trans->key >= firstNonTermId ) {
			long *inserted = prod->nonTermFirstSet.insert( trans->key );
			if ( inserted != 0 )
				modified = true;

			bool hasEpsilon = false;
			LangEl *lel = langElIndex[trans->key];
			for ( LelProdList::Iter ldef = lel->prodList; ldef.lte(); ldef++ ) {
				for ( ProdIdSet::Iter pid = ldef->nonTermFirstSet;
						pid.lte(); pid++ )
				{
					if ( *pid == -1 )
						hasEpsilon = true;
					else {
						long *inserted = prod->nonTermFirstSet.insert( *pid );
						if ( inserted != 0 )
							modified = true;
					}
				}
			}

			if ( hasEpsilon ) {
				if ( trans->value->toState->isFinState() ) {
					long *inserted = prod->nonTermFirstSet.insert( -1 );
					if ( inserted != 0 )
						modified = true;
				}

				bool lmod = makeNonTermFirstSetProd( prod, trans->value->toState );
				if ( lmod )
					modified = true;
			}
		}
	}
	return modified;
}


void Compiler::makeNonTermFirstSets()
{
	bool modified = true;
	while ( modified ) {
		modified = false;
		for ( ProdList::Iter prod = prodList; prod.lte(); prod++ ) {
			if ( prod->fsm->startState->isFinState() ) {
				long *inserted = prod->nonTermFirstSet.insert( -1 );
				if ( inserted != 0 )
					modified = true;
			}

			bool lmod = makeNonTermFirstSetProd( prod, prod->fsm->startState );
			if ( lmod )
				modified = true;
		}
	}

	for ( ProdList::Iter prod = prodList; prod.lte(); prod++ ) {
		if ( prod->nonTermFirstSet.find( prod->prodName->id ) )
			prod->isLeftRec = true;
	}
}

void Compiler::printNonTermFirstSets()
{
	for ( ProdList::Iter prod = prodList; prod.lte(); prod++ ) {
		cerr << prod->data << ": ";
		for ( ProdIdSet::Iter pid = prod->nonTermFirstSet; pid.lte(); pid++ )
		{
			if ( *pid < 0 )
				cerr << " <EPSILON>";
			else {
				LangEl *lel = langElIndex[*pid];
				cerr << " " << lel->name;
			}
		}
		cerr << endl;

		if ( prod->isLeftRec )
			cerr << "PROD IS LEFT REC: " << prod->data << endl;
	}
}

bool Compiler::makeFirstSetProd( Production *prod, PdaState *state )
{
	bool modified = false;
	for ( TransMap::Iter trans = state->transMap; trans.lte(); trans++ ) {
		if ( trans->key < firstNonTermId ) {
			long *inserted = prod->firstSet.insert( trans->key );
			if ( inserted != 0 )
				modified = true;
		}
		else {
			long *inserted = prod->firstSet.insert( trans->key );
			if ( inserted != 0 )
				modified = true;

			LangEl *klangEl = langElIndex[trans->key];
			if ( klangEl != 0 && klangEl->termDup != 0 ) {
				long *inserted2 = prod->firstSet.insert( klangEl->termDup->id );
				if ( inserted2 != 0 )
					modified = true;
			}

			bool hasEpsilon = false;
			LangEl *lel = langElIndex[trans->key];
			for ( LelProdList::Iter ldef = lel->prodList; ldef.lte(); ldef++ ) {
				for ( ProdIdSet::Iter pid = ldef->firstSet;
						pid.lte(); pid++ )
				{
					if ( *pid == -1 )
						hasEpsilon = true;
					else {
						long *inserted = prod->firstSet.insert( *pid );
						if ( inserted != 0 )
							modified = true;
					}
				}
			}

			if ( hasEpsilon ) {
				if ( trans->value->toState->isFinState() ) {
					long *inserted = prod->firstSet.insert( -1 );
					if ( inserted != 0 )
						modified = true;
				}

				bool lmod = makeFirstSetProd( prod, trans->value->toState );
				if ( lmod )
					modified = true;
			}
		}
	}
	return modified;
}


void Compiler::makeFirstSets()
{
	bool modified = true;
	while ( modified ) {
		modified = false;
		for ( ProdList::Iter prod = prodList; prod.lte(); prod++ ) {
			if ( prod->fsm->startState->isFinState() ) {
				long *inserted = prod->firstSet.insert( -1 );
				if ( inserted != 0 )
					modified = true;
			}

			bool lmod = makeFirstSetProd( prod, prod->fsm->startState );
			if ( lmod )
				modified = true;
		}
	}
}

void Compiler::printFirstSets()
{
	for ( ProdList::Iter prod = prodList; prod.lte(); prod++ ) {
		cerr << prod->data << ": ";
		for ( ProdIdSet::Iter pid = prod->firstSet; pid.lte(); pid++ )
		{
			if ( *pid < 0 )
				cerr << " <EPSILON>";
			else {
				LangEl *lel = langElIndex[*pid];
				if ( lel != 0 )
					cerr << endl << "    " << lel->name;
				else
					cerr << endl << "    " << *pid;
			}
		}
		cerr << endl;
	}
}

void Compiler::insertUniqueEmptyProductions()
{
	int limit = prodList.length();
	for ( ProdList::Iter prod = prodList; prod.lte(); prod++ ) {
		if ( prod->prodId == limit )
			break;

		/* Get a language element. */
		char name[20];
		snprintf(name, sizeof(name), "U%li", prodList.length());
		LangEl *prodName = addLangEl( this, rootNamespace, name, LangEl::NonTerm );
		Production *newDef = Production::cons( InputLoc(), prodName,
				0, String(), false, 0, prodList.length(), prodName->prodList.length() );
		prodName->prodList.append( newDef );
		prodList.append( newDef );

		prod->uniqueEmptyLeader = prodName;
	}
}

struct local_info *Compiler::makeLocalInfo( Locals &locals )
{
	struct local_info *localInfo = new local_info[locals.locals.length()];
	memset( localInfo, 0, sizeof(struct local_info) * locals.locals.length() );

	for ( Vector<LocalLoc>::Iter l = locals.locals; l.lte(); l++ ) {
		localInfo[l.pos()].type = (int) l->type;
		localInfo[l.pos()].offset = l->offset;
	}
	return localInfo;
}

short *Compiler::makeTrees( ObjectDef *objectDef, int &numTrees )
{
	numTrees = 0;
	for ( FieldList::Iter of = objectDef->fieldList; of.lte(); of++ ) {
		if ( of->value->exists() ) {
			UniqueType *ut = of->value->typeRef->resolveType( this );
			if ( ut->typeId == TYPE_TREE )
				numTrees += 1;
		}
	}

	short *trees = new short[numTrees];
	memset( trees, 0, sizeof(short) * numTrees );

	short pos = 0;
	for ( FieldList::Iter of = objectDef->fieldList; of.lte(); of++ ) {
		if ( of->value->exists() ) {
			UniqueType *ut = of->value->typeRef->resolveType( this );
			if ( ut->typeId == TYPE_TREE ) {
				trees[pos] = of->value->offset;
				pos += 1;
			}
		}
	}

	return trees;
}


void Compiler::makeRuntimeData()
{
	long count = 0;

	/*
	 * ProdLengths
	 * ProdLhsIs
	 * ProdNames
	 * ProdCodeBlocks
	 * ProdCodeBlockLens
	 */

	runtimeData->frame_info = new frame_info[nextFrameId];
	runtimeData->num_frames = nextFrameId;
	memset( runtimeData->frame_info, 0, sizeof(struct frame_info) * nextFrameId );

	/*
	 * Init code block.
	 */
	if ( rootCodeBlock == 0 ) {
		runtimeData->root_code = 0;
		runtimeData->root_code_len = 0;
		runtimeData->root_frame_id = 0;
	}
	else {
		runtimeData->root_code = rootCodeBlock->codeWC.data;
		runtimeData->root_code_len = rootCodeBlock->codeWC.length();
		runtimeData->root_frame_id = rootCodeBlock->frameId;
	}

	runtimeData->frame_info[rootCodeBlock->frameId].codeWV = 0;
	runtimeData->frame_info[rootCodeBlock->frameId].codeLenWV = 0;

	runtimeData->frame_info[rootCodeBlock->frameId].locals = makeLocalInfo( rootCodeBlock->locals );
	runtimeData->frame_info[rootCodeBlock->frameId].locals_len = rootCodeBlock->locals.locals.length();

	runtimeData->frame_info[rootCodeBlock->frameId].frame_size = rootLocalFrame->size();
	runtimeData->frame_info[rootCodeBlock->frameId].arg_size = 0;
	runtimeData->frame_info[rootCodeBlock->frameId].ret_tree = false;

	/*
	 * prodInfo
	 */
	count = prodList.length();
	runtimeData->prod_info = new prod_info[count];
	runtimeData->num_prods = count;

	count = 0;
	for ( ProdList::Iter prod = prodList; prod.lte(); prod++ ) {
		runtimeData->prod_info[count].lhs_id = prod->prodName->id;
		runtimeData->prod_info[count].prod_num = prod->prodNum;
		runtimeData->prod_info[count].length = prod->fsmLength;
		runtimeData->prod_info[count].name = prod->data;
		runtimeData->prod_info[count].frame_id = -1;

		CodeBlock *block = prod->redBlock;
		if ( block != 0 ) {
			runtimeData->prod_info[count].frame_id = block->frameId;
			runtimeData->frame_info[block->frameId].codeWV = block->codeWV.data;
			runtimeData->frame_info[block->frameId].codeLenWV = block->codeWV.length();

			runtimeData->frame_info[block->frameId].locals = makeLocalInfo( block->locals );
			runtimeData->frame_info[block->frameId].locals_len = block->locals.locals.length();

			runtimeData->frame_info[block->frameId].frame_size = block->localFrame->size();
			runtimeData->frame_info[block->frameId].arg_size = 0;
			runtimeData->frame_info[block->frameId].ret_tree = false;
		}

		runtimeData->prod_info[count].lhs_upref = true;
		runtimeData->prod_info[count].copy = prod->copy.data;
		runtimeData->prod_info[count].copy_len = prod->copy.length() / 2;
		count += 1;
	}

	/*
	 * regionInfo
	 */
	runtimeData->num_regions = regionList.length()+1;
	runtimeData->region_info = new region_info[runtimeData->num_regions];
	memset( runtimeData->region_info, 0,
			sizeof(struct region_info) * runtimeData->num_regions );

	runtimeData->region_info[0].default_token = -1;
	runtimeData->region_info[0].eof_frame_id = -1;
	runtimeData->region_info[0].ci_lel_id = 0;
	runtimeData->region_info[0].name = "pre";

	for ( RegionList::Iter reg = regionList; reg.lte(); reg++ ) {
		long regId = reg->id+1;
		runtimeData->region_info[regId].default_token =
				reg->impl->defaultTokenInstance == 0 ?
				-1 :
				reg->impl->defaultTokenInstance->tokenDef->tdLangEl->id;
		runtimeData->region_info[regId].eof_frame_id = -1;
		runtimeData->region_info[regId].ci_lel_id = reg->zeroLel != 0 ? reg->zeroLel->id : 0;

		{
			/* Label the region by where its lex block was declared. */
			char rbuf[1024];
			const char *fn = reg->loc.fileName != 0 ?
					reg->loc.fileName : "?";
			const char *base = strrchr( fn, '/' );
			if ( base != 0 )
				fn = base + 1;
			snprintf( rbuf, sizeof(rbuf), "%s:%d", fn, reg->loc.line );
			runtimeData->region_info[regId].name = strdup( rbuf );
		}

		CodeBlock *block = reg->preEofBlock;
		if ( block != 0 ) {
			runtimeData->region_info[regId].eof_frame_id = block->frameId;
			runtimeData->frame_info[block->frameId].codeWV = block->codeWV.data;
			runtimeData->frame_info[block->frameId].codeLenWV = block->codeWV.length();

			runtimeData->frame_info[block->frameId].locals = makeLocalInfo( block->locals );
			runtimeData->frame_info[block->frameId].locals_len = block->locals.locals.length();

			runtimeData->frame_info[block->frameId].frame_size = block->localFrame->size();
			runtimeData->frame_info[block->frameId].arg_size = 0;
			runtimeData->frame_info[block->frameId].ret_tree = false;
		}
	}

	/*
	 * lelInfo
	 */

	count = nextLelId;
	runtimeData->lel_info = new lang_el_info[count];
	runtimeData->num_lang_els = count;
	memset( runtimeData->lel_info, 0, sizeof(struct lang_el_info)*count );

	for ( int i = 0; i < nextLelId; i++ ) {
		LangEl *lel = langElIndex[i];
		if ( lel != 0 ) {
			assert( lel->id == i );
			runtimeData->lel_info[i].name = lel->fullLit;
			runtimeData->lel_info[i].xml_tag = lel->xmlTag;
			runtimeData->lel_info[i].repeat = lel->isRepeat;
			runtimeData->lel_info[i].list = lel->isList;
			runtimeData->lel_info[i].literal = lel->isLiteral;
			runtimeData->lel_info[i].ignore = lel->isIgnore;
			runtimeData->lel_info[i].frame_id = -1;

			CodeBlock *block = lel->transBlock;
			if ( block != 0 ) {
				runtimeData->lel_info[i].frame_id = block->frameId;
				runtimeData->frame_info[block->frameId].codeWV = block->codeWV.data;
				runtimeData->frame_info[block->frameId].codeLenWV = block->codeWV.length();

				runtimeData->frame_info[block->frameId].locals = makeLocalInfo( block->locals );
				runtimeData->frame_info[block->frameId].locals_len = block->locals.locals.length();

				runtimeData->frame_info[block->frameId].frame_size = block->localFrame->size();
				runtimeData->frame_info[block->frameId].arg_size = 0;
				runtimeData->frame_info[block->frameId].ret_tree = false;
			}

			runtimeData->lel_info[i].object_type_id =
					lel->objectDef == 0 ? 0 : lel->objectDef->id;
			runtimeData->lel_info[i].ofi_offset = lel->ofiOffset;
			runtimeData->lel_info[i].object_length =
					lel->objectDef != 0 ? lel->objectDef->size() : 0;

//			runtimeData->lelInfo[i].contextTypeId = 0;
//					lel->context == 0 ? 0 : lel->context->contextObjDef->id;
//			runtimeData->lelInfo[i].contextLength = 0; //lel->context == 0 ? 0 :
//					lel->context->contextObjDef->size();
//			if ( lel->context != 0 ) {
//				cout << "type: " << runtimeData->lelInfo[i].contextTypeId << " length: " <<
//					runtimeData->lelInfo[i].contextLength << endl;
//			}

			runtimeData->lel_info[i].term_dup_id = lel->termDup == 0 ? 0 : lel->termDup->id;

			if ( lel->tokenDef != 0 && lel->tokenDef->join != 0 &&
					lel->tokenDef->join->context != 0 )
				runtimeData->lel_info[i].mark_id = lel->tokenDef->join->mark->markId;
			else
				runtimeData->lel_info[i].mark_id = -1;

			runtimeData->lel_info[i].num_capture_attr = 0;
		}
		else {
			memset(&runtimeData->lel_info[i], 0, sizeof(struct lang_el_info) );
			runtimeData->lel_info[i].name = "__UNUSED";
			runtimeData->lel_info[i].xml_tag = "__UNUSED";
			runtimeData->lel_info[i].frame_id = -1;
		}
	}

	/*
	 * struct_el_info
	 */

	count = structEls.length();
	runtimeData->sel_info = new struct_el_info[count];
	runtimeData->num_struct_els = count;
	memset( runtimeData->sel_info, 0, sizeof(struct struct_el_info)*count );
	StructElList::Iter sel = structEls;
	for ( int i = 0; i < count; i++, sel++ ) {
		int treesLen;
		runtimeData->sel_info[i].size = sel->structDef->objectDef->size();
		runtimeData->sel_info[i].trees = makeTrees( sel->structDef->objectDef, treesLen );
		runtimeData->sel_info[i].trees_len = treesLen;
	}

	/*
	 * function_info
	 */
	count = functionList.length();

	runtimeData->function_info = new function_info[count];
	runtimeData->num_functions = count;
	memset( runtimeData->function_info, 0, sizeof(struct function_info)*count );
	for ( FunctionList::Iter func = functionList; func.lte(); func++ ) {

		runtimeData->function_info[func->funcId].frame_id = -1;

		CodeBlock *block = func->codeBlock;
		if ( block != 0 ) {
			runtimeData->function_info[func->funcId].frame_id = block->frameId;

			/* Name. */
			runtimeData->frame_info[block->frameId].name = func->name;

			/* Code. */
			runtimeData->frame_info[block->frameId].codeWV = block->codeWV.data;
			runtimeData->frame_info[block->frameId].codeLenWV = block->codeWV.length();
			runtimeData->frame_info[block->frameId].codeWC = block->codeWC.data;
			runtimeData->frame_info[block->frameId].codeLenWC = block->codeWC.length();

			/* Locals. */
			runtimeData->frame_info[block->frameId].locals = makeLocalInfo( block->locals );
			runtimeData->frame_info[block->frameId].locals_len = block->locals.locals.length();

			/* Meta. */
			runtimeData->frame_info[block->frameId].frame_size = func->localFrame->size();
			runtimeData->frame_info[block->frameId].arg_size = func->paramListSize;

			bool retTree = false;
			if ( func->typeRef ) {
				UniqueType *ut = func->typeRef->resolveType( this );
				retTree = ut->tree();
			}
			runtimeData->frame_info[block->frameId].ret_tree = retTree;
		}

		runtimeData->function_info[func->funcId].frame_size = func->localFrame->size();
		runtimeData->function_info[func->funcId].arg_size = func->paramListSize;
	}

	/*
	 * pat_cons_info
	 */

	/* Filled in later after patterns are parsed. */
	runtimeData->pat_repl_info = new pat_cons_info[nextPatConsId];
	memset( runtimeData->pat_repl_info, 0, sizeof(struct pat_cons_info) * nextPatConsId );
	runtimeData->num_patterns = nextPatConsId;
	runtimeData->pat_repl_nodes = 0;
	runtimeData->num_pattern_nodes = 0;


	/*
	 * generic_info
	 */
	count = 1;
	for ( NamespaceList::Iter nspace = namespaceList; nspace.lte(); nspace++ )
		count += nspace->genericList.length();
	assert( count == nextGenericId );

	runtimeData->generic_info = new generic_info[count];
	runtimeData->num_generics = count;
	memset( &runtimeData->generic_info[0], 0, sizeof(struct generic_info) );
	for ( NamespaceList::Iter nspace = namespaceList; nspace.lte(); nspace++ ) {
		for ( GenericList::Iter gen = nspace->genericList; gen.lte(); gen++ ) {
			runtimeData->generic_info[gen->id].type = gen->typeId;

			runtimeData->generic_info[gen->id].el_struct_id =
					( gen->typeId == GEN_MAP || gen->typeId == GEN_LIST ) ?
					gen->elUt->structEl->id : -1;
			runtimeData->generic_info[gen->id].el_offset =
					gen->el != 0 ? gen->el->offset : -1;

			runtimeData->generic_info[gen->id].key_type =
					gen->keyUt != 0 ? gen->keyUt->typeId : TYPE_NOTYPE;
			runtimeData->generic_info[gen->id].key_offset = 0;

			runtimeData->generic_info[gen->id].value_type =
					gen->valueUt != 0 ? gen->valueUt->typeId : TYPE_NOTYPE;
			runtimeData->generic_info[gen->id].value_offset = 0;

			runtimeData->generic_info[gen->id].parser_id =
					gen->typeId == GEN_PARSER ? gen->elUt->langEl->parserId : -1;
		}
	}

	runtimeData->argv_generic_id = argvTypeRef->generic->id;
	runtimeData->stds_generic_id = stdsTypeRef->generic->id;

	/*
	 * Literals
	 */
	runtimeData->num_literals = literalStrings.length();
	runtimeData->litdata = new const char *[literalStrings.length()];
	runtimeData->litlen = new long [literalStrings.length()];
	runtimeData->literals = 0;
	for ( StringMap::Iter el = literalStrings; el.lte(); el++ ) {
		/* Data. */
		char *data = new char[el->key.length()+1];
		memcpy( data, el->key.data, el->key.length() );
		data[el->key.length()] = 0;
		runtimeData->litdata[el->value] = data;

		/* Length. */
		runtimeData->litlen[el->value] = el->key.length();
	}

	/* Captured attributes. Loop over tokens and count first. */
	long numCapturedAttr = 0;
//	for ( RegionList::Iter reg = regionList; reg.lte(); reg++ ) {
//		for ( TokenInstanceListReg::Iter td = reg->tokenInstanceList; td.lte(); td++ )
//			numCapturedAttr += td->reCaptureVect.length();
//	}
	runtimeData->capture_attr = new CaptureAttr[numCapturedAttr];
	runtimeData->num_captured_attr = numCapturedAttr;
	memset( runtimeData->capture_attr, 0, sizeof( CaptureAttr ) * numCapturedAttr );

	count = 0;
//	for ( RegionList::Iter reg = regionList; reg.lte(); reg++ ) {
//		for ( TokenInstanceListReg::Iter td = reg->tokenInstanceList; td.lte(); td++ ) {
//			runtimeData->lelInfo[td->token->id].captureAttr = count;
//			runtimeData->lelInfo[td->token->id].numCaptureAttr = td->reCaptureVect.length();
//			for ( ReCaptureVect::Iter c = td->reCaptureVect; c.lte(); c++ ) {
//				runtimeData->captureAttr[count].mark_enter = c->markEnter->markId;
//				runtimeData->captureAttr[count].mark_leave = c->markLeave->markId;
//				runtimeData->captureAttr[count].offset = c->objField->offset;
//
//				count += 1;
//			}
//		}
//	}

	runtimeData->fsm_tables = fsmTables;
	runtimeData->pda_tables = pdaTables;

	/* FIXME: need a parser descriptor. */
	runtimeData->start_states = new int[nextParserId];
	runtimeData->eof_lel_ids = new int[nextParserId];
	runtimeData->parser_lel_ids = new int[nextParserId];
	runtimeData->num_parsers = nextParserId;
	for ( LelList::Iter lel = langEls; lel.lte(); lel++ ) {
		if ( lel->parserId >= 0 ) {
			runtimeData->start_states[lel->parserId] = lel->startState->stateNum;
			runtimeData->eof_lel_ids[lel->parserId] = lel->eofLel->id;
			runtimeData->parser_lel_ids[lel->parserId] = lel->id;
		}
	}

	runtimeData->global_size = globalObjectDef->size();

	/*
	 * Exports.
	 */
	count = 0;
	for ( FieldList::Iter of = globalObjectDef->fieldList; of.lte(); of++ ) {
		ObjectField *field = of->value;
		if ( field->isExport ) {
			count += 1;
		}
	}

	runtimeData->num_exports = count;
	if ( count == 0 ) {
		runtimeData->export_info = 0;
	}
	else {
		runtimeData->export_info = new export_info[count];

		long i = 0;
		for ( FieldList::Iter of = globalObjectDef->fieldList; of.lte(); of++ ) {
			ObjectField *field = of->value;
			if ( field->isExport ) {
				runtimeData->export_info[i].name = strdup( field->name );
				runtimeData->export_info[i].global_id = field->offset;
				i += 1;
			}
		}
	}


	/*
	 * Boundary between terms and non-terms.
	 */
	runtimeData->first_non_term_id = firstNonTermId;

	/*
	 * Boundary between trees and structs
	 */
	runtimeData->first_struct_el_id = firstStructElId;

	/* Special trees. */
	runtimeData->integer_id = -1; //intLangEl->id;
	runtimeData->string_id = strLangEl->id;
	runtimeData->any_id = anyLangEl->id;
	runtimeData->eof_id = 0; //eofLangEl->id;
	runtimeData->no_token_id = noTokenLangEl->id;
	runtimeData->global_id = globalSel->id;
	runtimeData->argv_el_id = argvElSel->id;
	runtimeData->stds_el_id = stdsElSel->id;
	runtimeData->struct_inbuilt_id = structInbuiltId;
	runtimeData->struct_stream_id = structStreamId;
	runtimeData->struct_input_id = structInputId;

	runtimeData->fsm_execute = &internalFsmExecute;
	runtimeData->send_named_lang_el = &internalSendNamedLangEl;
	runtimeData->init_bindings = &internalInitBindings;
	runtimeData->pop_binding = &internalPopBinding;

	runtimeData->host_call = &internal_host_call;
	runtimeData->commit_reduce_forward = &internal_commit_reduce_forward;
	runtimeData->commit_union_sz = &internal_commit_union_sz;
	runtimeData->init_need = &internal_init_need;
	runtimeData->reducer_need_tok = &internal_reducer_need_tok;
	runtimeData->reducer_need_ign = &internal_reducer_need_ign;
}

/* Borrow alg->state for mapsTo. */
void countNodes( program_t *prg, int &count, parse_tree_t *parseTree, kid_t *kid )
{
	if ( kid != 0 ) {
		count += 1;

		/* Should't have to recurse here. */
		tree_t *ignoreList = tree_left_ignore( prg, kid->tree );
		if ( ignoreList != 0 ) {
			kid_t *ignore = ignoreList->child;
			while ( ignore != 0 ) {
				count += 1;
				ignore = ignore->next;
			}
		}

		ignoreList = tree_right_ignore( prg, kid->tree );
		if ( ignoreList != 0 ) {
			kid_t *ignore = ignoreList->child;
			while ( ignore != 0 ) {
				count += 1;
				ignore = ignore->next;
			}
		}

		//count += prg->rtd->lelInfo[kid->tree->id].numCaptureAttr;

		if ( !( parseTree->flags & PF_NAMED ) &&
				!( parseTree->flags & PF_ARTIFICIAL ) &&
				tree_child( prg, kid->tree ) != 0 )
		{
			countNodes( prg, count, parseTree->child, tree_child( prg, kid->tree ) );
		}
		countNodes( prg, count, parseTree->next, kid->next );
	}
}

void fillNodes( program_t *prg, int &nextAvail, struct bindings *bindings, long &bindId,
		struct pat_cons_node *nodes, parse_tree_t *parseTree, kid_t *kid, int ind )
{
	if ( kid != 0 ) {
		struct pat_cons_node &node = nodes[ind];

		kid_t *child =
			!( parseTree->flags & PF_NAMED ) &&
			!( parseTree->flags & PF_ARTIFICIAL ) &&
			tree_child( prg, kid->tree ) != 0
			?
			tree_child( prg, kid->tree ) : 0;

		parse_tree_t *ptChild =
			!( parseTree->flags & PF_NAMED ) &&
			!( parseTree->flags & PF_ARTIFICIAL ) &&
			tree_child( prg, kid->tree ) != 0
			?
			parseTree->child : 0;

		/* Set up the fields. */
		node.id = kid->tree->id;
		node.prod_num = kid->tree->prod_num;
		node.length = string_length( kid->tree->tokdata );
		node.data = string_data( kid->tree->tokdata );

		/* Ignore items. */
		tree_t *ignoreList = tree_left_ignore( prg, kid->tree );
		kid_t *ignore = ignoreList == 0 ? 0 : ignoreList->child;
		node.left_ignore = ignore == 0 ? -1 : nextAvail;

		while ( ignore != 0 ) {
			struct pat_cons_node &node = nodes[nextAvail++];

			memset( &node, 0, sizeof(struct pat_cons_node) );
			node.id = ignore->tree->id;
			node.prod_num = ignore->tree->prod_num;
			node.next = ignore->next == 0 ? -1 : nextAvail;

			node.length = string_length( ignore->tree->tokdata );
			node.data = string_data( ignore->tree->tokdata );

			ignore = ignore->next;
		}

		/* Ignore items. */
		ignoreList = tree_right_ignore( prg, kid->tree );
		ignore = ignoreList == 0 ? 0 : ignoreList->child;
		node.right_ignore = ignore == 0 ? -1 : nextAvail;

		while ( ignore != 0 ) {
			struct pat_cons_node &node = nodes[nextAvail++];

			memset( &node, 0, sizeof(struct pat_cons_node) );
			node.id = ignore->tree->id;
			node.prod_num = ignore->tree->prod_num;
			node.next = ignore->next == 0 ? -1 : nextAvail;

			node.length = string_length( ignore->tree->tokdata );
			node.data = string_data( ignore->tree->tokdata );

			ignore = ignore->next;
		}

		///* The captured attributes. */
		//for ( int i = 0; i < prg->rtd->lelInfo[kid->tree->id].numCaptureAttr; i++ ) {
		//	CaptureAttr *cap = prg->rtd->captureAttr +
		//			prg->rtd->lelInfo[kid->tree->id].captureAttr + i;
		//
		//	tree_t *attr = colm_get_attr( kid->tree, cap->offset );
		//
		//	struct pat_cons_node &node = nodes[nextAvail++];
		//	memset( &node, 0, sizeof(struct pat_cons_node) );
		//
		//	node.id = attr->id;
		//	node.prodNum = attr->prodNum;
		//	node.length = stringLength( attr->tokdata );
		//	node.data = stringData( attr->tokdata );
		//}

		node.stop = parseTree->flags & PF_TERM_DUP;

		node.child = child == 0 ? -1 : nextAvail++;

		/* Recurse. */
		fillNodes( prg, nextAvail, bindings, bindId, nodes, ptChild, child, node.child );

		/* Since the parser is bottom up the bindings are in a bottom up
		 * traversal order. Check after recursing. */
		node.bind_id = 0;
		if ( bindId < bindings->length() && bindings->data[bindId] == parseTree ) {
			/* Remember that binding ids are indexed from one. */
			node.bind_id = bindId++;

			//cout << "binding match in " << __PRETTY_FUNCTION__ << endl;
			//cout << "bindId: " << node.bindId << endl;
		}

		node.next = kid->next == 0 ? -1 : nextAvail++;

		/* Move to the next child. */
		fillNodes( prg, nextAvail, bindings, bindId, nodes, parseTree->next, kid->next, node.next );
	}
}

void Compiler::fillInPatterns( program_t *prg )
{
	/*
	 * patReplNodes
	 */

	/* Count is referenced and computed by mapNode. */
	int count = 0;
	for ( PatList::Iter pat = patternList; pat.lte(); pat++ ) {
		countNodes( prg, count,
				pat->pdaRun->stack_top->next,
				pat->pdaRun->stack_top->next->shadow );
	}

	for ( ConsList::Iter repl = replList; repl.lte(); repl++ ) {
		countNodes( prg, count,
				repl->pdaRun->stack_top->next,
				repl->pdaRun->stack_top->next->shadow );
	}

	runtimeData->pat_repl_nodes = new pat_cons_node[count];
	runtimeData->num_pattern_nodes = count;

	int nextAvail = 0;

	for ( PatList::Iter pat = patternList; pat.lte(); pat++ ) {
		int ind = nextAvail++;
		runtimeData->pat_repl_info[pat->patRepId].offset = ind;

		/* BindIds are indexed base one. */
		runtimeData->pat_repl_info[pat->patRepId].num_bindings =
				pat->pdaRun->bindings->length() - 1;

		/* Init the bind */
		long bindId = 1;
		fillNodes( prg, nextAvail, pat->pdaRun->bindings, bindId,
				runtimeData->pat_repl_nodes,
				pat->pdaRun->stack_top->next,
				pat->pdaRun->stack_top->next->shadow,
				ind );
	}

	for ( ConsList::Iter repl = replList; repl.lte(); repl++ ) {
		int ind = nextAvail++;
		runtimeData->pat_repl_info[repl->patRepId].offset = ind;

		/* BindIds are indexed base one. */
		runtimeData->pat_repl_info[repl->patRepId].num_bindings =
				repl->pdaRun->bindings->length() - 1;

		long bindId = 1;
		fillNodes( prg, nextAvail, repl->pdaRun->bindings, bindId,
				runtimeData->pat_repl_nodes,
				repl->pdaRun->stack_top->next,
				repl->pdaRun->stack_top->next->shadow,
				ind );
	}

	assert( nextAvail == count );
}


int Compiler::findIndexOff( struct pda_tables *pdaTables, PdaGraph *pdaGraph, PdaState *state, int &curLen )
{
	for ( int start = 0; start < curLen;  ) {
		int offset = start;
		for ( TransMap::Iter trans = state->transMap; trans.lte(); trans++ ) {
			if ( pdaTables->owners[offset] != -1 )
				goto next_start;

			offset++;
			if ( ! trans.last() ) {
				TransMap::Iter next = trans.next();
				offset += next->key - trans->key - 1;
			}
		}

		/* Got though the whole list without a conflict. */
		return start;

next_start:
		start++;
	}

	return curLen;
}

struct CmpSpan
{
	static int compare( PdaState *state1, PdaState *state2 )
	{
		int dist1 = 0, dist2 = 0;

		if ( state1->transMap.length() > 0 ) {
			TransMap::Iter first1 = state1->transMap.first();
			TransMap::Iter last1 = state1->transMap.last();
			dist1 = last1->key - first1->key;
		}

		if ( state2->transMap.length() > 0 ) {
			TransMap::Iter first2 = state2->transMap.first();
			TransMap::Iter last2 = state2->transMap.last();
			dist2 = last2->key - first2->key;
		}

		if ( dist1 < dist2 )
			return 1;
		else if ( dist2 < dist1 )
			return -1;
		return 0;
	}
};

PdaGraph *Compiler::makePdaGraph( LangElSet &parserEls )
{
	//for ( ProdList::Iter prod = prodList; prod.lte(); prod++ )
	//	cerr << prod->prodId << " " << prod->data << endl;

	PdaGraph *pdaGraph = new PdaGraph();
	lalr1GenerateParser( pdaGraph, parserEls );
	pdaGraph->setStateNumbers();
	analyzeMachine( pdaGraph, parserEls );

	//cerr << "NUMBER OF STATES: " << pdaGraph->stateList.length() << endl;

	return pdaGraph;
}

struct pda_tables *Compiler::makePdaTables( PdaGraph *pdaGraph )
{
	int count, pos;
	struct pda_tables *pdaTables = new pda_tables;

	/*
	 * Counting max indices.
	 */
	count = 0;
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		for ( TransMap::Iter trans = state->transMap; trans.lte(); trans++ ) {
			count++;
			if ( ! trans.last() ) {
				TransMap::Iter next = trans.next();
				count +=  next->key - trans->key - 1;
			}
		}
	}


	/* Allocate indices and owners. */
	pdaTables->num_indices = count;
	pdaTables->indices = new int[count];
	pdaTables->owners = new int[count];
	for ( long i = 0; i < count; i++ ) {
		pdaTables->indices[i] = -1;
		pdaTables->owners[i] = -1;
	}

	/* Allocate offsets. */
	int numStates = pdaGraph->stateList.length();
	pdaTables->offsets = new unsigned int[numStates];
	pdaTables->num_states = numStates;

	/* Place transitions into indices/owners */
	PdaState **states = new PdaState*[numStates];
	long ds = 0;
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ )
		states[ds++] = state;

	/* Sorting baseded on span length. Gives an improvement, but incures a
	 * cost. Off for now. */
	//MergeSort< PdaState*, CmpSpan > mergeSort;
	//mergeSort.sort( states, numStates );

	int indLen = 0;
	for ( int s = 0; s < numStates; s++ ) {
		PdaState *state = states[s];

		int indOff = findIndexOff( pdaTables, pdaGraph, state, indLen );
		pdaTables->offsets[state->stateNum] = indOff;

		for ( TransMap::Iter trans = state->transMap; trans.lte(); trans++ ) {
			pdaTables->indices[indOff] = trans->value->actionSetEl->key.id;
			pdaTables->owners[indOff] = state->stateNum;
			indOff++;

			if ( ! trans.last() ) {
				TransMap::Iter next = trans.next();
				indOff += next->key - trans->key - 1;
			}
		}

		if ( indOff > indLen )
			indLen = indOff;
	}

	/* We allocated the max, but cmpression gives us less. */
	pdaTables->num_indices = indLen;
	delete[] states;


	/*
	 * Keys
	 */
	count = pdaGraph->stateList.length() * 2;;
	pdaTables->keys = new int[count];
	pdaTables->num_keys = count;

	count = 0;
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		if ( state->transMap.length() == 0 ) {
			pdaTables->keys[count+0] = 0;
			pdaTables->keys[count+1] = 0;
		}
		else {
			TransMap::Iter first = state->transMap.first();
			TransMap::Iter last = state->transMap.last();
			pdaTables->keys[count+0] = first->key;
			pdaTables->keys[count+1] = last->key;
		}
		count += 2;
	}

	/*
	 * Targs
	 */
	count = pdaGraph->actionSet.length();
	pdaTables->targs = new unsigned int[count];
	pdaTables->num_targs = count;

	count = 0;
	for ( PdaActionSet::Iter asi = pdaGraph->actionSet; asi.lte(); asi++ )
		pdaTables->targs[count++] = asi->key.targ;

	/*
	 * ActInds
	 */
	count = pdaGraph->actionSet.length();
	pdaTables->act_inds = new unsigned int[count];
	pdaTables->num_act_inds = count;

	count = pos = 0;
	for ( PdaActionSet::Iter asi = pdaGraph->actionSet; asi.lte(); asi++ ) {
		pdaTables->act_inds[count++] = pos;
		pos += asi->key.actions.length() + 1;
	}

	/*
	 * Actions
	 */
	count = 0;
	for ( PdaActionSet::Iter asi = pdaGraph->actionSet; asi.lte(); asi++ )
		count += asi->key.actions.length() + 1;

	pdaTables->actions = new unsigned int[count];
	pdaTables->num_actions = count;

	count = 0;
	for ( PdaActionSet::Iter asi = pdaGraph->actionSet; asi.lte(); asi++ ) {
		for ( ActDataList::Iter ali = asi->key.actions; ali.lte(); ali++ )
			pdaTables->actions[count++] = *ali;

		pdaTables->actions[count++] = 0;
	}

	/*
	 * CommitLen
	 */
	count = pdaGraph->actionSet.length();
	pdaTables->commit_len = new int[count];
	pdaTables->num_commit_len = count;

	count = 0;
	for ( PdaActionSet::Iter asi = pdaGraph->actionSet; asi.lte(); asi++ )
		pdaTables->commit_len[count++] = asi->key.commitLen;

	/*
	 * tokenRegionInds. Start at one so region index 0 is null (unset).
	 */
	count = 0;
	pos = 1;
	pdaTables->token_region_inds = new int[pdaTables->num_states];
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		pdaTables->token_region_inds[count++] = pos;
		pos += state->regions.length() + 1;
	}


	/*
	 * tokenRegions. Build in a null at the beginning.
	 */

	count = 1;
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ )
		count += state->regions.length() + 1;

	pdaTables->num_region_items = count;
	pdaTables->token_regions = new int[pdaTables->num_region_items];

	count = 0;
	pdaTables->token_regions[count++] = 0;
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		for ( RegionVect::Iter reg = state->regions; reg.lte(); reg++ ) {
			int id = ( *reg == EOF_REGION ) ? 0 : (*reg)->id + 1;
			pdaTables->token_regions[count++] = id;
		}

		pdaTables->token_regions[count++] = 0;
	}

	/*
	 * tokenPreRegions. Build in a null at the beginning.
	 */

	count = 1;
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ )
		count += state->regions.length() + 1;

	pdaTables->num_pre_region_items = count;
	pdaTables->token_pre_regions = new int[pdaTables->num_pre_region_items];

	count = 0;
	pdaTables->token_pre_regions[count++] = 0;
	for ( PdaStateList::Iter state = pdaGraph->stateList; state.lte(); state++ ) {
		for ( RegionVect::Iter reg = state->regions; reg.lte(); reg++ ) {
			assert( state->preRegions.length() <= 1 );
			if ( state->preRegions.length() == 0 || state->preRegions[0]->impl->wasEmpty )
				pdaTables->token_pre_regions[count++] = -1;
			else
				pdaTables->token_pre_regions[count++] = state->preRegions[0]->id + 1;
		}

		pdaTables->token_pre_regions[count++] = 0;
	}


	return pdaTables;
}

void Compiler::makeParser( LangElSet &parserEls )
{
	pdaGraph = makePdaGraph( parserEls );
	pdaTables = makePdaTables( pdaGraph );
}

