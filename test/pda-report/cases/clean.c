#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include <colm/pdarun.h>
#include <colm/debug.h>
#include <colm/bytecode.h>
#include <colm/defs.h>
#include <colm/input.h>
#include <colm/tree.h>
#include <colm/program.h>
#include <colm/colm.h>

extern struct colm_sections colm_object;

#define parser_start 1
#define parser_first_final 1
#define parser_error 0
#define false 0
#define true 1

static long parser_entry_by_region[] = {
	0, 1, 3, 4, 4
};

static struct fsm_tables fsmTables_start =
{
	0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
	parser_entry_by_region,

	0,  0,  0,  0,  0,  0,  0,  0,
	4,

	parser_start,
	parser_first_final,
	parser_error,

	0,
	0
};

static void fsm_execute( struct pda_run *pdaRun, struct input_impl *inputStream )
{
	pdaRun->start = pdaRun->p;
/*_resume:*/
	if ( pdaRun->fsm_cs == 0 )
		goto out;
	if ( pdaRun->p == pdaRun->pe )
		goto out_switch;
	--pdaRun->p;

	switch ( pdaRun->fsm_cs )
	{
tr3:
	{	pdaRun->p += 1;
{ pdaRun->tokend = pdaRun->tokpref + ( pdaRun->p - pdaRun->start ); }	pdaRun->matched_token = 4;
	goto out;
}
	goto st1;
tr4:
	{{ pdaRun->tokend = pdaRun->tokpref + ( pdaRun->p - pdaRun->start ); }	pdaRun->matched_token = 5;
	goto out;
}
	goto st1;
st1:
case 1:
	if ( ++pdaRun->p == pdaRun->pe )
		goto out1;
	{pdaRun->tokstart = pdaRun->p;}
	switch( (*pdaRun->p) ) {
		case 13: goto st2;
		case 32: goto st2;
		case 110: goto tr3;
	}
	if ( 9 <= (*pdaRun->p) && (*pdaRun->p) <= 10 )
		goto st2;
	goto st0;
st0:
	goto out0;
st2:
case 2:
	if ( ++pdaRun->p == pdaRun->pe )
		goto out2;
	switch( (*pdaRun->p) ) {
		case 13: goto st2;
		case 32: goto st2;
	}
	if ( 9 <= (*pdaRun->p) && (*pdaRun->p) <= 10 )
		goto st2;
	goto tr4;
tr6:
	{	pdaRun->p += 1;
{ pdaRun->tokend = pdaRun->tokpref + ( pdaRun->p - pdaRun->start ); }	pdaRun->matched_token = 4;
	goto out;
}
	goto st3;
st3:
case 3:
	if ( ++pdaRun->p == pdaRun->pe )
		goto out3;
	{pdaRun->tokstart = pdaRun->p;}
	if ( (*pdaRun->p) == 110 )
		goto tr6;
	goto st0;
tr9:
	{{ pdaRun->tokend = pdaRun->tokpref + ( pdaRun->p - pdaRun->start ); }	pdaRun->matched_token = 5;
	goto out;
}
	goto st4;
st4:
case 4:
	if ( ++pdaRun->p == pdaRun->pe )
		goto out4;
	{pdaRun->tokstart = pdaRun->p;}
	switch( (*pdaRun->p) ) {
		case 13: goto st5;
		case 32: goto st5;
	}
	if ( 9 <= (*pdaRun->p) && (*pdaRun->p) <= 10 )
		goto st5;
	goto st0;
st5:
case 5:
	if ( ++pdaRun->p == pdaRun->pe )
		goto out5;
	switch( (*pdaRun->p) ) {
		case 13: goto st5;
		case 32: goto st5;
	}
	if ( 9 <= (*pdaRun->p) && (*pdaRun->p) <= 10 )
		goto st5;
	goto tr9;
	}
out_switch:
	switch ( pdaRun->fsm_cs )
	{
	case 1: out1: pdaRun->fsm_cs = 1; goto out; 
	case 0: out0: pdaRun->fsm_cs = 0; goto out; 
	case 2: out2: if ( pdaRun->scan_eof ) {goto tr4;
}pdaRun->fsm_cs = 2; goto out; 
	case 3: out3: pdaRun->fsm_cs = 3; goto out; 
	case 4: out4: pdaRun->fsm_cs = 4; goto out; 
	case 5: out5: if ( pdaRun->scan_eof ) {goto tr9;
}pdaRun->fsm_cs = 5; goto out; 
	}
out:
	if ( pdaRun->p != 0 )
		pdaRun->tokpref += pdaRun->p - pdaRun->start;
}

static void sendNamedLangEl( struct colm_program *prg, tree_t **tree,
		struct pda_run *pda_run, struct input_impl *input ) { }
static void initBindings( struct pda_run *pdaRun ) {}
static void popBinding( struct pda_run *pdaRun, parse_tree_t *tree ) {}


static int pid_0_parser_indices[] = {
	2, 3, 4, 5, 0, 1, -1, -1, 
	-1, -1, -1, -1, -1, -1, -1, -1, 
	-1, -1, -1, -1, 0, 1
};

static int pid_0_parser_owners[] = {
	0, 1, 2, 3, 0, 0, -1, -1, 
	-1, -1, -1, -1, -1, -1, -1, -1, 
	-1, -1, -1, -1, 0, 0
};

static int pid_0_parser_keys[] = {
	4, 25, 16, 16, 16, 16, 16, 16, 
	0, 0
};

static unsigned int pid_0_parser_offsets[] = {
	0, 1, 2, 3, 0
};

static unsigned int pid_0_parser_targs[] = {
	1, 2, 3, 4, 4, 4
};

static unsigned int pid_0_parser_actInds[] = {
	0, 2, 4, 6, 8, 10
};

static unsigned int pid_0_parser_actions[] = {
	1, 0, 1, 0, 1, 0, 1, 0, 
	2, 0, 6, 0
};

static int pid_0_parser_commitLen[] = {
	0, 0, 0, 0, 0, 0
};

static int pid_0_parser_tokenRegionInds[] = {
	1, 3, 5, 7, 9
};

static int pid_0_parser_tokenRegions[] = {
	0, 1, 0, 0, 0, 0, 0, 0, 
	0, 0
};

static int pid_0_parser_tokenPreRegions[] = {
	0, -1, 0, -1, 0, -1, 0, 3, 
	0, 0
};

static struct pda_tables pid_0_pdaTables =
{
	pid_0_parser_indices,
	pid_0_parser_owners,
	pid_0_parser_keys,
	pid_0_parser_offsets,
	pid_0_parser_targs,
	pid_0_parser_actInds,
	pid_0_parser_actions,
	pid_0_parser_commitLen,
	pid_0_parser_tokenRegionInds,
	pid_0_parser_tokenRegions,
	pid_0_parser_tokenPreRegions,

	22,
	10,
	5,
	6,
	6,
	12,
	6,
	10,
	10
};

static struct local_info locals_0[] = {
	{ 1, -1 }
};

static unsigned char copy_0[] = {
	0, 0
};

static code_t parser_rootCode[] = {
	237, 14, 2, 0, 237, 13, 1, 0, 
	237, 15, 0, 0, 59, 1, 0, 0, 
	0, 117, 190, 16, 0, 182, 173, 184, 
	173, 52, 215, 1, 0, 219, 215, 0, 
	0, 53, 63, 255, 255, 49, 237, 1
};

static struct lang_el_info parser_lelInfo[] = {
/*    0 */ { "__UNUSED",  "__UNUSED", 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0 },
/*    1 */ { "ptr",  "ptr", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*    2 */ { "str",  "str", 0, 0, 0, 0, -1, 10, 0, 0, 0, -1, 0, 0 },
/*    3 */ { "il",  "il", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*    4 */ { "`n",  "_literal_0001", 0, 0, 1, 0, -1, 5, 0, 0, 0, -1, 0, 0 },
/*    5 */ { "_ignore_0003",  "_ignore_0003", 0, 0, 0, 1, -1, 6, 0, 0, 0, -1, 0, 0 },
/*    6 */ { "_ign_0",  "_ign_0", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*    7 */ { "_T_any",  "_T_any", 0, 0, 0, 0, -1, 0, 0, 0, 23, -1, 0, 0 },
/*    8 */ { "_T_start",  "_T_start", 0, 0, 0, 0, -1, 7, 0, 0, 24, -1, 0, 0 },
/*    9 */ { "_T_exp",  "_T_exp", 0, 0, 0, 0, -1, 8, 0, 0, 25, -1, 0, 0 },
/*   10 */ { "_eof_ptr",  "_eof_ptr", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   11 */ { "_eof_str",  "_eof_str", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   12 */ { "_eof_il",  "_eof_il", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   13 */ { "_eof_any",  "_eof_any", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   14 */ { "_eof__literal_0001",  "_eof__literal_0001", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   15 */ { "_eof__ignore_0003",  "_eof__ignore_0003", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   16 */ { "_eof_start",  "_eof_start", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   17 */ { "_eof_exp",  "_eof_exp", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   18 */ { "_eof__ign_0",  "_eof__ign_0", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   19 */ { "_eof__T_any",  "_eof__T_any", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   20 */ { "_eof__T_start",  "_eof__T_start", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   21 */ { "_eof__T_exp",  "_eof__T_exp", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   22 */ { "_notoken",  "_notoken", 0, 0, 0, 1, -1, 0, 0, 0, 0, -1, 0, 0 },
/*   23 */ { "any",  "any", 0, 0, 0, 0, -1, 0, 0, 0, 7, -1, 0, 0 },
/*   24 */ { "start",  "start", 0, 0, 0, 0, -1, 7, 0, 0, 8, -1, 0, 0 },
/*   25 */ { "exp",  "exp", 0, 0, 0, 0, -1, 8, 0, 0, 9, -1, 0, 0 },
/*   26 */ { "_root",  "_root", 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0 }
};

static short struct_trees_0[] = {
	2, 
};

static short struct_trees_4[] = {
	0, 
};

static struct struct_el_info parser_selInfo[] = {
	{ 3, struct_trees_0, 1,  },
	{ 0, 0, 0,  },
	{ 0, 0, 0,  },
	{ 3, 0, 0,  },
	{ 3, struct_trees_4, 1,  },

};

static struct frame_info parser_frameInfo[] = {
	{ "", 0, 0, 0, 0, locals_0, 1, 0, 1 }
};

static struct prod_info parser_prodInfo[] = {
	{ 24, 0, 1, "start-1", -1, 1, copy_0, 1,  },
	{ 25, 0, 1, "exp-1", -1, 1, 0, 0,  },
	{ 26, 0, 1, "_root-1", -1, 1, 0, 0,  },
	{ 26, 1, 1, "_root-2", -1, 1, 0, 0,  },
	{ 26, 2, 1, "_root-3", -1, 1, 0, 0,  },
	{ 26, 3, 1, "_root-4", -1, 1, 0, 0,  },
	{ 26, 4, 1, "_root-5", -1, 1, 0, 0,  },
	{ 26, 5, 1, "_root-6", -1, 1, 0, 0,  },
	{ 26, 6, 1, "_root-7", -1, 1, 0, 0,  },
	{ 26, 7, 1, "_root-8", -1, 1, 0, 0,  },
	{ 26, 8, 1, "_root-9", -1, 1, 0, 0,  },
	{ 26, 9, 1, "_root-10", -1, 1, 0, 0,  },
	{ 26, 10, 1, "_root-11", -1, 1, 0, 0,  },
	{ 26, 11, 1, "_root-12", -1, 1, 0, 0,  },
	{ 26, 12, 1, "_root-13", -1, 1, 0, 0,  },
	{ 26, 13, 1, "_root-14", -1, 1, 0, 0,  },
	{ 26, 14, 1, "_root-15", -1, 1, 0, 0,  },
	{ 26, 15, 1, "_root-16", -1, 1, 0, 0,  },
	{ 26, 16, 1, "_root-17", -1, 1, 0, 0,  },
	{ 26, 17, 1, "_root-18", -1, 1, 0, 0,  },
	{ 26, 18, 1, "_root-19", -1, 1, 0, 0,  },
	{ 26, 19, 1, "_root-20", -1, 1, 0, 0,  },
	{ 26, 20, 1, "_root-21", -1, 1, 0, 0,  },
	{ 26, 21, 1, "_root-22", -1, 1, 0, 0,  },
	{ 26, 22, 1, "_root-23", -1, 1, 0, 0,  },
	{ 26, 23, 1, "_root-24", -1, 1, 0, 0,  },
	{ 26, 24, 1, "_root-25", -1, 1, 0, 0,  },
	{ 26, 25, 1, "_root-26", -1, 1, 0, 0,  }
};

static struct pat_cons_info parser_patReplInfo[] = {
};

static struct pat_cons_node parser_patReplNodes[] = {
};

static struct function_info parser_functionInfo[] = {

};

static struct region_info parser_regionInfo[] = {
	{ -1, -1, 0 },
	{ -1, -1, 0 },
	{ -1, -1, 0 },
	{ -1, -1, 0 },
	{ -1, -1, 6 }
};

static struct generic_info parser_genericInfo[] = {
	{ 0, 0, 0, 0, 0, 0, 0, 0 },
	{ 20, -1, -1, 0, 0, 0, 0, 0 },
	{ 21, 30, 1, 0, 0, 5, 0, -1 },
	{ 21, 31, 1, 0, 0, 2, 0, -1 },
};

static const char *parser_litdata[] = {
	"unwind code\n",
};

static long parser_litlen[] = {
	12, };

static head_t *parser_literals[] = {
	0, };

static int startStates[] = {
	0, };

static int eofLelIds[] = {
	16, };

static int parserLelIds[] = {
	24, };

static CaptureAttr captureAttr[] = {
};

tree_t **colm_object_host_call( program_t *prg, long code, tree_t **sp );
void colm_object_commit_reduce_forward( program_t *prg, tree_t **root,
		struct pda_run *pda_run, parse_tree_t *pt );
long colm_object_commit_union_sz( int reducer );
void colm_object_init_need();
int colm_object_reducer_need_tok( program_t *prg, struct pda_run *pda_run, int id );
int colm_object_reducer_need_ign( program_t *prg, struct pda_run *pda_run );
void colm_object_read_reduce( program_t *prg, int reducer, input_t *stream );

static struct export_info parser_exportInfo[] = {
};

struct colm_sections colm_object = 
{
	parser_lelInfo,
	27,

	parser_selInfo,
	5,

	parser_prodInfo,
	28,

	parser_regionInfo,
	5,

	parser_rootCode,
	40,
	0,

	parser_frameInfo,
	1,

	parser_functionInfo,
	0,

	parser_patReplInfo,
	0,

	parser_patReplNodes,
	0,

	parser_genericInfo,
	4,

	parser_exportInfo,
	0,

	3,
	2,

	parser_litdata,
	parser_litlen,
	parser_literals,
	1,

	captureAttr,
	0,

	&fsmTables_start,
	&pid_0_pdaTables,
	startStates, eofLelIds, parserLelIds, 1,

	3,

	23,
	27,
	-1,
	2,
	23,
	0,
	22,
	27,
	31,
	30,
	32,
	32,
	34,
	&fsm_execute,
	&sendNamedLangEl,
	&initBindings,
	&popBinding,
	&colm_object_host_call,
	&colm_object_commit_reduce_forward,
	&colm_object_commit_union_sz,
	&colm_object_init_need,
	&colm_object_reducer_need_tok,
	&colm_object_reducer_need_ign,
	&colm_object_read_reduce,
};

tree_t **colm_object_host_call( program_t *prg, long code, tree_t **sp )
{
	value_t rtn = 0;
	switch ( code ) {
	}
	vm_push_value( rtn );
	return sp;
}
void colm_object_commit_reduce_forward( program_t *prg, tree_t **root,
		struct pda_run *pda_run, parse_tree_t *pt )
{
	commit_clear_parse_tree( prg, root, pda_run, pt->child );
}

long colm_object_commit_union_sz( int reducer ) { return 0; }
void colm_object_init_need() {}
int colm_object_reducer_need_tok( program_t *prg, struct pda_run *pda_run, int id ) { return COLM_RN_BOTH; }
int colm_object_reducer_need_ign( program_t *prg, struct pda_run *pda_run ) { return COLM_RN_BOTH; }

void colm_object_read_reduce( program_t *prg, int reducer, input_t *stream ) {}
int main( int argc, const char **argv )
{
	struct colm_program *prg;
	int exit_status;

	prg = colm_new_program( &colm_object );
	colm_set_debug( prg, 0 );
	colm_run_program( prg, argc, argv );
	exit_status = colm_delete_program( prg );
	return exit_status;
}

