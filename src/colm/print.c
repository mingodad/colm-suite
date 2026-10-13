/*
 * Copyright 2007-2018 Adrian Thurston <thurston@colm.net>
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

#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>
#include <unistd.h>
#include <assert.h>

#include <colm/tree.h>
#include <colm/pool.h>
#include <colm/bytecode.h>
#include <colm/debug.h>

#define BUFFER_INITIAL_SIZE 4096

static void xml_escape_data( struct colm_print_args *print_args, const char *data, long len )
{
	int i;
	for ( i = 0; i < len; i++ ) {
		if ( data[i] == '<' )
			print_args->out( print_args, "&lt;", 4 );
		else if ( data[i] == '>' )
			print_args->out( print_args, "&gt;", 4 );
		else if ( data[i] == '&' )
			print_args->out( print_args, "&amp;", 5 );
		else if ( (32 <= data[i] && data[i] <= 126) ||
				data[i] == '\t' || data[i] == '\n' || data[i] == '\r' )
		{
			print_args->out( print_args, &data[i], 1 );
		}
		else {
			char out[64];
			snprintf( out, sizeof(out), "&#%u;", ((unsigned)data[i]) );
			print_args->out( print_args, out, strlen(out) );
		}
	}
}

void init_str_collect( str_collect_t *collect )
{
	collect->data = malloc( BUFFER_INITIAL_SIZE );
	collect->allocated = BUFFER_INITIAL_SIZE;
	collect->length = 0;
	collect->indent.indent = 0;
	collect->indent.level = COLM_INDENT_OFF;
}

void str_collect_destroy( str_collect_t *collect )
{
	free( collect->data );
}

void str_collect_append( str_collect_t *collect, const char *data, long len )
{
	long new_len = collect->length + len;
	if ( new_len > collect->allocated ) {
		collect->allocated = new_len * 2;
		collect->data = realloc( collect->data, collect->allocated );
	}
	memcpy( collect->data + collect->length, data, len );
	collect->length += len;
}

void str_collect_clear( str_collect_t *collect )
{
	collect->length = 0;
}

#define INT_SZ 32

static void print_str( struct colm_print_args *print_args, head_t *str )
{
	print_args->out( print_args, str->data, str->length );
}

static void append_collect( struct colm_print_args *args, const char *data, int length )
{
	str_collect_append( (str_collect_t*) args->arg, data, length );
}

static void append_file( struct colm_print_args *args, const char *data, int length )
{
	struct stream_impl_data *impl = (struct stream_impl_data*) args->arg;
	fwrite( data, 1, length, impl->file );
}

static void out_indent( struct colm_print_args *args, const char *data, int length )
{
	int level;
restart:
	if ( args->indent->indent ) {
		/* Consume mode. */
		while ( length > 0 && ( *data == ' ' || *data == '\t' ) ) {
			data += 1;
			length -= 1;
		}

		if ( length > 0 ) {
			/* Found some data, print the indentation and turn off indentation
			 * mode. */
			for ( level = 0; level < args->indent->level; level++ )
				args->out( args, "\t", 1 );

			args->indent->indent = 0;

			goto restart;
		}
	}
	else {
		const char *nl;
		if ( args->indent->level != COLM_INDENT_OFF &&
				(nl = memchr( data, '\n', length )) )
		{
			/* Print up to and including the newline. */
			int wl = nl - data + 1;
			args->out( args, data, wl );

			/* Go into consume state. If we see more non-indentation chars we
			 * will generate the appropriate indentation level. */
			data += wl;
			length -= wl;
			args->indent->indent = 1;
			goto restart;
		}
		else {
			/* Indentation off, or no indent trigger (newline). */
			args->out( args, data, length );
		}
	}
}


tree_t *tree_trim( struct colm_program *prg, tree_t **sp, tree_t *tree )
{
	if ( tree == 0 )
		return 0;

	debug( prg, REALM_PARSE, "attaching left ignore\n" );

	/* Make the ignore list for the left-ignore. */
	tree_t *left_ignore = tree_allocate( prg );
	left_ignore->id = LEL_ID_IGNORE;
	left_ignore->flags |= AF_SUPPRESS_RIGHT;

	tree = push_left_ignore( prg, tree, left_ignore );

	debug( prg, REALM_PARSE, "attaching ignore right\n" );

	/* Copy the ignore list first if we need to attach it as a right
	 * ignore. */
	tree_t *right_ignore = 0;
	right_ignore = tree_allocate( prg );
	right_ignore->id = LEL_ID_IGNORE;
	right_ignore->flags |= AF_SUPPRESS_LEFT;

	tree = push_right_ignore( prg, tree, right_ignore );

	return tree;
}

enum ReturnType
{
	Done = 1,
	CollectIgnoreLeft,
	CollectIgnoreRight,
	RecIgnoreList,
	ChildPrint
};

enum VisitType
{
	IgnoreWrapper,
	IgnoreData,
	Term,
	NonTerm
};

#define TF_TERM_SEEN 0x1

static void print_kid( program_t *prg, tree_t **sp, struct colm_print_args *print_args, kid_t *kid )
{
	enum ReturnType rt;
	kid_t *parent = 0;
	kid_t *leading_ignore = 0;
	enum VisitType visit_type;
	int flags = 0;

	/* Iterate the kids passed in. We are expecting a next, which will allow us
	 * to print the trailing ignore list. */
	while ( kid != 0 ) {
		vm_push_type( enum ReturnType, Done );
		goto rec_call;
		rec_return_top:
		kid = kid->next;
	}

	return;

rec_call:
	if ( kid->tree == 0 )
		goto skip_null;

	/* If not currently skipping ignore data, then print it. Ignore data can
	 * be associated with terminals and nonterminals. */
	if ( kid->tree->flags & AF_LEFT_IGNORE ) {
		vm_push_kid( parent );
		vm_push_kid( kid );
		parent = kid;
		kid = tree_left_ignore_kid( prg, kid->tree );
		vm_push_type( enum ReturnType, CollectIgnoreLeft );
		goto rec_call;
		rec_return_ign_left:
		kid = vm_pop_kid();
		parent = vm_pop_kid();
	}

	if ( kid->tree->id == LEL_ID_IGNORE )
		visit_type = IgnoreWrapper;
	else if ( parent != 0 && parent->tree->id == LEL_ID_IGNORE )
		visit_type = IgnoreData;
	else if ( kid->tree->id < prg->rtd->first_non_term_id )
		visit_type = Term;
	else
		visit_type = NonTerm;

	debug( prg, REALM_PRINT, "visit type: %d\n", visit_type );

	if ( visit_type == IgnoreData ) {
		debug( prg, REALM_PRINT, "putting %p on ignore list\n", kid->tree );
		kid_t *new_ignore = kid_allocate( prg );
		new_ignore->next = leading_ignore;
		leading_ignore = new_ignore;
		leading_ignore->tree = kid->tree;
		goto skip_node;
	}

	if ( visit_type == IgnoreWrapper ) {
		kid_t *new_ignore = kid_allocate( prg );
		new_ignore->next = leading_ignore;
		leading_ignore = new_ignore;
		leading_ignore->tree = kid->tree;
		/* Don't skip. */
	}

	/* print leading ignore? Triggered by terminals. */
	if ( visit_type == Term ) {
		/* Reverse the leading ignore list. */
		if ( leading_ignore != 0 ) {
			kid_t *ignore = 0, *last = 0;

			/* Reverse the list and take the opportunity to implement the
			 * suppress left. */
			while ( true ) {
				kid_t *next = leading_ignore->next;
				leading_ignore->next = last;

				if ( leading_ignore->tree->flags & AF_SUPPRESS_LEFT ) {
					/* We are moving left. Chop off the tail. */
					debug( prg, REALM_PRINT, "suppressing left\n" );
					free_kid_list( prg, next );
					break;
				}

				if ( next == 0 )
					break;

				last = leading_ignore;
				leading_ignore = next;
			}

			/* Print the leading ignore list. Also implement the suppress right
			 * in the process. */
			if ( print_args->comm && (!print_args->trim ||
					(flags & TF_TERM_SEEN && kid->tree->id > 0)) )
			{
				ignore = leading_ignore;
				while ( ignore != 0 ) {
					if ( ignore->tree->flags & AF_SUPPRESS_RIGHT )
						break;

					if ( ignore->tree->id != LEL_ID_IGNORE ) {
						vm_push_type( enum VisitType, visit_type );
						vm_push_kid( leading_ignore );
						vm_push_kid( ignore );
						vm_push_kid( parent );
						vm_push_kid( kid );

						leading_ignore = 0;
						kid = ignore;
						parent = 0;

						debug( prg, REALM_PRINT, "rec call on %p\n", kid->tree );
						vm_push_type( enum ReturnType, RecIgnoreList );
						goto rec_call;
						rec_return_il:

						kid = vm_pop_kid();
						parent = vm_pop_kid();
						ignore = vm_pop_kid();
						leading_ignore = vm_pop_kid();
						visit_type = vm_pop_type(enum VisitType);
					}

					ignore = ignore->next;
				}
			}

			/* Free the leading ignore list. */
			free_kid_list( prg, leading_ignore );
			leading_ignore = 0;
		}
	}

	if ( visit_type == Term || visit_type == NonTerm ) {
		/* Open the tree. */
		print_args->open_tree( prg, sp, print_args, parent, kid );
	}

	if ( visit_type == Term )
		flags |= TF_TERM_SEEN;

	if ( visit_type == Term || visit_type == IgnoreData ) {
		/* Print contents. */
		if ( kid->tree->id < prg->rtd->first_non_term_id ) {
			debug( prg, REALM_PRINT, "printing terminal %p\n", kid->tree );
			if ( kid->tree->id != 0 )
				print_args->print_term( prg, sp, print_args, kid );
		}
	}

	/* Print children. */
	kid_t *child = print_args->attr ?
		tree_attr( prg, kid->tree ) :
		tree_child( prg, kid->tree );

	if ( child != 0 ) {
		vm_push_type( enum VisitType, visit_type );
		vm_push_kid( parent );
		vm_push_kid( kid );
		parent = kid;
		kid = child;
		while ( kid != 0 ) {
			vm_push_type( enum ReturnType, ChildPrint );
			goto rec_call;
			rec_return:
			kid = kid->next;
		}
		kid = vm_pop_kid();
		parent = vm_pop_kid();
		visit_type = vm_pop_type(enum VisitType);
	}

	if ( visit_type == Term || visit_type == NonTerm ) {
		/* close the tree. */
		print_args->close_tree( prg, sp, print_args, parent, kid );
	}

skip_node:

	/* If not currently skipping ignore data, then print it. Ignore data can
	 * be associated with terminals and nonterminals. */
	if ( kid->tree->flags & AF_RIGHT_IGNORE ) {
		debug( prg, REALM_PRINT, "right ignore\n" );
		vm_push_kid( parent );
		vm_push_kid( kid );
		parent = kid;
		kid = tree_right_ignore_kid( prg, kid->tree );
		vm_push_type( enum ReturnType, CollectIgnoreRight );
		goto rec_call;
		rec_return_ign_right:
		kid = vm_pop_kid();
		parent = vm_pop_kid();
	}

/* For skiping over content on null. */
skip_null:

	rt = vm_pop_type(enum ReturnType);
	switch ( rt ) {
		case Done:
			debug( prg, REALM_PRINT, "return: done\n" );
			goto rec_return_top;
			break;
		case CollectIgnoreLeft:
			debug( prg, REALM_PRINT, "return: ignore left\n" );
			goto rec_return_ign_left;
		case CollectIgnoreRight:
			debug( prg, REALM_PRINT, "return: ignore right\n" );
			goto rec_return_ign_right;
		case RecIgnoreList:
			debug( prg, REALM_PRINT, "return: ignore list\n" );
			goto rec_return_il;
		case ChildPrint:
			debug( prg, REALM_PRINT, "return: child print\n" );
			goto rec_return;
	}
}

void colm_print_tree_args( program_t *prg, tree_t **sp,
		struct colm_print_args *print_args, tree_t *tree )
{
	if ( tree == 0 )
		out_indent( print_args, "NIL", 3 );
	else {
		/* This term tree allows us to print trailing ignores. */
		tree_t term_tree;
		memset( &term_tree, 0, sizeof(term_tree) );

		kid_t kid, term;
		term.tree = &term_tree;
		term.next = 0;

		kid.tree = tree;
		kid.next = &term;

		print_kid( prg, sp, print_args, &kid );
	}
}

void colm_print_null( program_t *prg, tree_t **sp,
		struct colm_print_args *args, kid_t *parent, kid_t *kid )
{
}

void colm_print_term_tree( program_t *prg, tree_t **sp,
		struct colm_print_args *args, kid_t *kid )
{
	debug( prg, REALM_PRINT, "printing term %p\n", kid->tree );

	if ( kid->tree->id == LEL_ID_PTR ) {
		char buf[INT_SZ];
		out_indent( args, "#<", 2 );
		snprintf( buf, sizeof(buf), "%lx", ((pointer_t*)kid->tree)->value );
		out_indent( args, buf, strlen(buf) );
		out_indent( args, ">", 1 );
	}
	else if ( kid->tree->id == LEL_ID_STR ) {
		print_str( args, ((str_t*)kid->tree)->value );
	}
//	else if ( kid->tree->id == LEL_ID_STREAM ) {
//		char buf[INT_SZ];
//		printArgs->out( printArgs, "#", 1 );
//		sprintf( buf, "%p", (void*) ((stream_t*)kid->tree)->in->file );
//		printArgs->out( printArgs, buf, strlen(buf) );
//	}
	else if ( kid->tree->tokdata != 0 &&
			string_length( kid->tree->tokdata ) > 0 )
	{
		out_indent( args, string_data( kid->tree->tokdata ),
				string_length( kid->tree->tokdata ) );
	}

	struct lang_el_info *lel_info = prg->rtd->lel_info;
	if ( strcmp( lel_info[kid->tree->id].name, "_IN_" ) == 0 ) {
		if ( args->indent->level == COLM_INDENT_OFF ) {
			args->indent->level = 1;
			args->indent->indent = 1;
		}
		else {
			args->indent->level += 1;
		}
	}

	if ( strcmp( lel_info[kid->tree->id].name, "_EX_" ) == 0 )
		args->indent->level -= 1;
}

void colm_print_tree_collect( program_t *prg, tree_t **sp,
		str_collect_t *collect, tree_t *tree, int trim )
{
	struct colm_print_args print_args = {
			collect, true, false, trim, &collect->indent,
			&append_collect, &colm_print_null,
			&colm_print_term_tree, &colm_print_null
	};

	colm_print_tree_args( prg, sp, &print_args, tree );
}

void colm_print_tree_collect_a( program_t *prg, tree_t **sp,
		str_collect_t *collect, tree_t *tree, int trim )
{
	struct colm_print_args print_args = {
			collect, true, true, trim, &collect->indent,
			&append_collect, &colm_print_null,
			&colm_print_term_tree, &colm_print_null
	};

	colm_print_tree_args( prg, sp, &print_args, tree );
}

void colm_print_tree_file( program_t *prg, tree_t **sp,
		struct stream_impl_data *impl, tree_t *tree, int trim )
{
	struct colm_print_args print_args = {
			impl, true, false, trim, &impl->indent,
			&append_file, &colm_print_null,
			&colm_print_term_tree, &colm_print_null
	};

	colm_print_tree_args( prg, sp, &print_args, tree );
}

static void xml_open( program_t *prg, tree_t **sp, struct colm_print_args *args,
		kid_t *parent, kid_t *kid )
{
	/* Skip the terminal that is for forcing trailing ignores out. */
	if ( kid->tree->id == 0 )
		return;

	struct lang_el_info *lel_info = prg->rtd->lel_info;

	/* List flattening: skip the repeats and lists that are a continuation of
	 * the list. */
	if ( parent != 0 && parent->tree->id == kid->tree->id && kid->next == 0 &&
			( lel_info[parent->tree->id].repeat || lel_info[parent->tree->id].list ) )
	{
		return;
	}

	const char *name = lel_info[kid->tree->id].xml_tag;
	args->out( args, "<", 1 );
	args->out( args, name, strlen( name ) );
	args->out( args, ">", 1 );
}

static void xml_term( program_t *prg, tree_t **sp,
	struct colm_print_args *print_args, kid_t *kid )
{
	//kid_t *child;

	/*child = */ tree_child( prg, kid->tree );
	if ( kid->tree->id == LEL_ID_PTR ) {
		char ptr[INT_SZ];
		snprintf( ptr, sizeof(ptr), "%lx", ((pointer_t*)kid->tree)->value );
		print_args->out( print_args, ptr, strlen(ptr) );
	}
	else if ( kid->tree->id == LEL_ID_STR ) {
		head_t *head = (head_t*) ((str_t*)kid->tree)->value;

		xml_escape_data( print_args, head->data, head->length );
	}
	else if ( 0 < kid->tree->id && kid->tree->id < prg->rtd->first_non_term_id &&
			kid->tree->id != LEL_ID_IGNORE &&
			kid->tree->tokdata != 0 &&
			string_length( kid->tree->tokdata ) > 0 )
	{
		xml_escape_data( print_args, string_data( kid->tree->tokdata ),
				string_length( kid->tree->tokdata ) );
	}
}

static void xml_close( program_t *prg, tree_t **sp,
		struct colm_print_args *args, kid_t *parent, kid_t *kid )
{
	/* Skip the terminal that is for forcing trailing ignores out. */
	if ( kid->tree->id == 0 )
		return;

	struct lang_el_info *lel_info = prg->rtd->lel_info;

	/* List flattening: skip the repeats and lists that are a continuation of
	 * the list. */
	if ( parent != 0 && parent->tree->id == kid->tree->id && kid->next == 0 &&
			( lel_info[parent->tree->id].repeat || lel_info[parent->tree->id].list ) )
	{
		return;
	}

	const char *name = lel_info[kid->tree->id].xml_tag;
	args->out( args, "</", 2 );
	args->out( args, name, strlen( name ) );
	args->out( args, ">", 1 );
}

void colm_print_xml_stdout( program_t *prg, tree_t **sp,
		struct stream_impl_data *impl, tree_t *tree,
		int comm_attr, int trim )
{
	struct colm_print_args print_args = {
			impl, comm_attr, comm_attr, trim, &impl->indent,
			&append_file, &xml_open, &xml_term, &xml_close };
	colm_print_tree_args( prg, sp, &print_args, tree );
}

static void postfix_open( program_t *prg, tree_t **sp, struct colm_print_args *args,
		kid_t *parent, kid_t *kid )
{
}

static void postfix_term_data( struct colm_print_args *args, const char *data, long len )
{
	int i;
	for ( i = 0; i < len; i++ ) {
		if ( data[i] == '\\' )
			args->out( args, "\\5c", 3 );
		else if ( 33 <= data[i] && data[i] <= 126 )
			args->out( args, &data[i], 1 );
		else {
			char out[64];
			snprintf( out, sizeof(out), "\\%02x", ((unsigned char)data[i]) );
			args->out( args, out, strlen(out) );
		}
	}
}

static void postfix_term( program_t *prg, tree_t **sp,
		struct colm_print_args *args, kid_t *kid )
{
	//kid_t *child;

	/*child = */ tree_child( prg, kid->tree );
	if ( kid->tree->id == LEL_ID_PTR ) {
		//char ptr[INT_SZ];
		//sprintf( ptr, "%lx", ((pointer_t*)kid->tree)->value );
		//args->out( args, ptr, strlen(ptr) );
		args->out( args, "p\n", 2 );
	}
	else if ( kid->tree->id == LEL_ID_STR ) {
		//head_t *head = (head_t*) ((str_t*)kid->tree)->value;

		//xml_escape_data( args, (char*)(head->data), head->length );
		args->out( args, "s\n", 2 );
	}
	else if ( 0 < kid->tree->id && kid->tree->id < prg->rtd->first_non_term_id &&
			kid->tree->id != LEL_ID_IGNORE //&&
			//kid->tree->tokdata != 0 &&
			//string_length( kid->tree->tokdata ) > 0 )
			)
	{
		char buf[512];
		struct lang_el_info *lel_info = prg->rtd->lel_info;
		const char *name = lel_info[kid->tree->id].xml_tag;

		args->out( args, "t ", 2 );
		args->out( args, name, strlen( name ) );

		/* id. */
		snprintf( buf, sizeof(buf), " %d", kid->tree->id );
		args->out( args, buf, strlen( buf ) );

		/* location. */
		if ( kid->tree->tokdata == 0 ) {
			args->out( args, " 0 0 0 -", 8 );
		}
		else {
			struct colm_data *tokdata = kid->tree->tokdata;
			struct colm_location *loc = tokdata->location;
			if ( loc == 0 ) {
				args->out( args, " 0 0 0 ", 7 );
			}
			else {
				snprintf( buf, sizeof(buf), " %ld %ld %ld ", loc->line, loc->column, loc->byte );
				args->out( args, buf, strlen( buf ) );
			}

			if ( string_length( tokdata ) == 0 ) {
				args->out( args, "-", 1 );
			}
			else {
				postfix_term_data( args, string_data( tokdata ), string_length( tokdata ) );
			}
		}

		args->out( args, "\n", 1 );
	}
}

static void postfix_close( program_t *prg, tree_t **sp,
		struct colm_print_args *args, kid_t *parent, kid_t *kid )
{
	/* Skip the terminal that is for forcing trailing ignores out. */
	if ( kid->tree->id == 0 )
		return;

	if ( kid->tree->id >= prg->rtd->first_non_term_id ) {
		char buf[512];
		struct lang_el_info *lel_info = prg->rtd->lel_info;
		const char *name = lel_info[kid->tree->id].xml_tag;

		args->out( args, "r ", 2 );
		args->out( args, name, strlen( name ) );

		/* id. */
		snprintf( buf, sizeof(buf), " %d", kid->tree->id );
		args->out( args, buf, strlen( buf ) );

		/* Production number. */
		snprintf( buf, sizeof(buf), " %d", kid->tree->prod_num );
		args->out( args, buf, strlen( buf ) );

		/* Child count. */
		int children = 0;
		kid_t *child = tree_child( prg, kid->tree );
		while ( child != 0 ) {
			child = child->next;
			children += 1;
		}

		snprintf( buf, sizeof(buf), " %d", children );
		args->out( args, buf, strlen( buf ) );
		args->out( args, "\n", 1 );
	}
}

void colm_postfix_tree_collect( program_t *prg, tree_t **sp,
		str_collect_t *collect, tree_t *tree, int trim )
{
	struct colm_print_args print_args = {
		collect, false, false, false, &collect->indent,
		&append_collect, &postfix_open, &postfix_term, &postfix_close
	};

	colm_print_tree_args( prg, sp, &print_args, tree );
}

#if 0
void colm_postfix_tree_file( program_t *prg, tree_t **sp, struct stream_impl *impl,
		tree_t *tree, int trim )
{
	struct colm_print_args print_args = {
			impl, false, false, false, &append_file,
			&postfix_open, &postfix_term, &postfix_close
	};

	colm_print_tree_args( prg, sp, &print_args, tree );

	//struct stream_impl *impl = (struct stream_impl*) args->arg;
	fflush( impl->file );
}
#endif

void colm_print_tree_collect_xml( program_t *prg, tree_t **sp,
		str_collect_t *collect, tree_t *tree, int trim )
{
	struct colm_print_args print_args = {
			collect, false, false, trim, &collect->indent,
			&append_collect, &xml_open, &xml_term, &xml_close
	};

	colm_print_tree_args( prg, sp, &print_args, tree );
}

void colm_print_tree_collect_xml_ac( program_t *prg, tree_t **sp,
		str_collect_t *collect, tree_t *tree, int trim )
{
	struct colm_print_args print_args = {
			collect, true, true, trim, &collect->indent,
			&append_collect, &xml_open, &xml_term, &xml_close
	};

	colm_print_tree_args( prg, sp, &print_args, tree );
}

#define CST_MAX_DEPTH 1024

struct cst_print_ctx {
    str_collect_t *collect;
    int depth;
    int last[CST_MAX_DEPTH];
};

static void cst_out( struct colm_print_args *args,
        const char *data, int length )
{
    struct cst_print_ctx *ctx = args->arg;
    str_collect_append( ctx->collect, data, length );
}

static void cst_open( program_t *prg, tree_t **sp,
        struct colm_print_args *args, kid_t *parent, kid_t *kid )
{
    struct cst_print_ctx *ctx = args->arg;
    struct lang_el_info *lel_info = prg->rtd->lel_info;

    /* Terminals are printed by cst_term(). */
    if ( kid->tree->id < prg->rtd->first_non_term_id )
        return;

    /* Draw ancestor continuation prefixes. */
    for ( int i = 0; i < ctx->depth; i++ ) {
        const char *prefix = ctx->last[i] ? "   " : "│  ";
        args->out( args, prefix, strlen(prefix) );
    }

    /* Draw a branch for every node except the root. */
    if ( parent != 0 ) {
        const char *branch = kid->next == 0 ? "└─ " : "├─ ";
        args->out( args, branch, strlen(branch) );
    }

    const char *name = lel_info[kid->tree->id].name;
    args->out( args, name, strlen(name) );

    //char buf[128];
    //snprintf( buf, sizeof(buf), " (prod=%d)", kid->tree->prod_num );
    //args->out( args, buf, strlen(buf) );
    args->out( args, "\n", 1 );

    if ( ctx->depth < CST_MAX_DEPTH ) {
        ctx->last[ctx->depth] = kid->next == 0;
        ctx->depth++;
    }
}

static void cst_term( program_t *prg, tree_t **sp,
        struct colm_print_args *args, kid_t *kid )
{
    struct cst_print_ctx *ctx = args->arg;
    struct lang_el_info *lel_info = prg->rtd->lel_info;

    /* Draw ancestor continuation prefixes. */
    for ( int i = 0; i < ctx->depth; i++ ) {
        const char *prefix = ctx->last[i] ? "   " : "│  ";
        args->out( args, prefix, strlen(prefix) );
    }

    /* Draw the terminal branch. */
    const char *branch = kid->next == 0 ? "└─ " : "├─ ";
    args->out( args, branch, strlen(branch) );

    if ( kid->tree->id <= 0 ||
            kid->tree->id >= prg->rtd->first_non_term_id ||
            kid->tree->id == LEL_ID_IGNORE )
        return;

    for ( int i = 0; i < args->indent->level; i++ )
        args->out( args, "   ", 3 );

    const char *name = lel_info[kid->tree->id].name;
    args->out( args, name, strlen(name) );
    args->out( args, ": ", 2 );

    if ( kid->tree->tokdata != 0 ) {
        const char *data = string_data( kid->tree->tokdata );
        int len = string_length( kid->tree->tokdata );
        args->out( args, data, len );
    }

    args->out( args, "\n", 1 );
}

static void cst_close( program_t *prg, tree_t **sp,
        struct colm_print_args *args, kid_t *parent, kid_t *kid )
{
    struct cst_print_ctx *ctx = args->arg;

    if ( kid->tree->id < prg->rtd->first_non_term_id )
        return;

    if ( ctx->depth > 0 )
        ctx->depth--;
}

void colm_cst_tree_collect( program_t *prg, tree_t **sp,
        str_collect_t *collect, tree_t *tree, int trim )
{
    struct cst_print_ctx ctx = { .collect = collect };
    struct indent_impl indent = { 0, 0 };

    struct colm_print_args print_args = {
        &ctx, false, false, trim, &indent,
        &cst_out, &cst_open, &cst_term, &cst_close
    };

    colm_print_tree_args( prg, sp, &print_args, tree );
}

/* A deliberately self-contained CST printer. This is a draft alternative to
 * colm_cst_tree_collect; it does not use the callback-based generic printer
 * above. Ignore wrappers and attributes are omitted through tree_child(). */
struct cst_simple_ctx {
    program_t *prg;
    str_collect_t *collect;
    int last[CST_MAX_DEPTH];
};

static void cst_simple_append( str_collect_t *collect, const char *data )
{
    str_collect_append( collect, data, strlen( data ) );
}

static void cst_simple_prefix( struct cst_simple_ctx *ctx, int depth,
        int is_last, int root )
{
    int i;
    for ( i = 0; i < depth; i++ )
        cst_simple_append( ctx->collect, ctx->last[i] ? "   " : "│  " );

    if ( !root )
        cst_simple_append( ctx->collect, is_last ? "└─ " : "├─ " );
}

static void cst_simple_node( struct cst_simple_ctx *ctx, tree_t *tree,
        int depth, int is_last, int root )
{
    struct lang_el_info *lel_info = ctx->prg->rtd->lel_info;
    kid_t *kid;
    int child_depth;

    if ( tree == 0 || tree->id <= 0 || tree->id == LEL_ID_IGNORE )
        return;

    if ( tree->id < ctx->prg->rtd->first_non_term_id ) {
        cst_simple_prefix( ctx, depth, is_last, root );
        cst_simple_append( ctx->collect, lel_info[tree->id].name );
        cst_simple_append( ctx->collect, ": " );

        if ( tree->tokdata != 0 )
            str_collect_append( ctx->collect,
                    string_data( tree->tokdata ),
                    string_length( tree->tokdata ) );

        cst_simple_append( ctx->collect, "\n" );
        return;
    }

    cst_simple_prefix( ctx, depth, is_last, root );
    cst_simple_append( ctx->collect, lel_info[tree->id].name );
    cst_simple_append( ctx->collect, "\n" );

    child_depth = depth;
    if ( child_depth < CST_MAX_DEPTH ) {
        ctx->last[child_depth] = is_last;
        child_depth += 1;
    }

    kid = tree_child( ctx->prg, tree );
    while ( kid != 0 ) {
        cst_simple_node( ctx, kid->tree, child_depth,
                kid->next == 0, false );
        kid = kid->next;
    }
}

void colm_cst_tree_collect_simple( program_t *prg, tree_t **sp,
        str_collect_t *collect, tree_t *tree, int trim )
{
    struct cst_simple_ctx ctx;

    (void)sp;
    (void)trim;

    ctx.prg = prg;
    ctx.collect = collect;
    memset( ctx.last, 0, sizeof(ctx.last) );
    cst_simple_node( &ctx, tree, 0, true, true );
}

struct cst_filtered_ctx {
    program_t *prg;
    str_collect_t *collect;
    const char * const *hidden_prefixes;
    const char *show_list;
    int last[CST_MAX_DEPTH];
};

/* Is name one of the comma-separated exact type names in list? */
static bool cst_type_in_list( const char *name, const char *list )
{
    const char *p = list;
    size_t name_len = strlen( name );

    while ( *p != 0 ) {
        const char *start = p;
        size_t len;

        while ( *p != 0 && *p != ',' ) p++;

        while ( start < p && ( *start == ' ' || *start == '\t' ) ) start++;
        len = p - start;
        while ( len > 0 && ( start[len-1] == ' ' || start[len-1] == '\t' ) )
            len--;

        if ( len == name_len && strncmp( name, start, len ) == 0 )
            return true;

        if ( *p == ',' ) p++;
    }

    return false;
}

static bool cst_filtered_hidden( struct cst_filtered_ctx *ctx, tree_t *tree )
{
    struct lang_el_info *lel_info = ctx->prg->rtd->lel_info;
    const char *name;
    int i;

    if ( tree == 0 || tree->id <= 0 || tree->id == LEL_ID_IGNORE )
        return false;

    name = lel_info[tree->id].name;
    if ( name == 0 )
        return false;

    /* A show-list filters by exact name; anything not listed is elided. */
    if ( ctx->show_list != 0 )
        return !cst_type_in_list( name, ctx->show_list );

    if ( tree->id < ctx->prg->rtd->first_non_term_id ||
            ctx->hidden_prefixes == 0 )
        return false;

    for ( i = 0; ctx->hidden_prefixes[i] != 0; i++ ) {
        size_t length = strlen( ctx->hidden_prefixes[i] );
        if ( strncmp( name, ctx->hidden_prefixes[i], length ) == 0 )
            return true;
    }

    return false;
}

static void cst_filtered_prefix( struct cst_filtered_ctx *ctx, int depth,
        int is_last, int root )
{
    int i;
    for ( i = 0; i < depth; i++ )
        cst_simple_append( ctx->collect, ctx->last[i] ? "   " : "│  " );

    if ( !root )
        cst_simple_append( ctx->collect, is_last ? "└─ " : "├─ " );
}

static void cst_filtered_node( struct cst_filtered_ctx *ctx, tree_t *tree,
        int depth, int is_last, int root )
{
    struct lang_el_info *lel_info = ctx->prg->rtd->lel_info;
    kid_t *kid;
    int child_depth;

    if ( tree == 0 || tree->id <= 0 || tree->id == LEL_ID_IGNORE )
        return;

    if ( cst_filtered_hidden( ctx, tree ) ) {
        kid = tree_child( ctx->prg, tree );
        while ( kid != 0 ) {
            cst_filtered_node( ctx, kid->tree, depth,
                    kid->next == 0, root );
            kid = kid->next;
        }
        return;
    }

    cst_filtered_prefix( ctx, depth, is_last, root );

    if ( tree->id < ctx->prg->rtd->first_non_term_id ) {
        cst_simple_append( ctx->collect, lel_info[tree->id].name );
        cst_simple_append( ctx->collect, ": " );

        if ( tree->tokdata != 0 )
            str_collect_append( ctx->collect,
                    string_data( tree->tokdata ),
                    string_length( tree->tokdata ) );

        cst_simple_append( ctx->collect, "\n" );
        return;
    }

    cst_simple_append( ctx->collect, lel_info[tree->id].name );
    cst_simple_append( ctx->collect, "\n" );

    child_depth = depth;
    if ( child_depth < CST_MAX_DEPTH ) {
        ctx->last[child_depth] = is_last;
        child_depth += 1;
    }

    kid = tree_child( ctx->prg, tree );
    while ( kid != 0 ) {
        cst_filtered_node( ctx, kid->tree, child_depth,
                kid->next == 0, false );
        kid = kid->next;
    }
}

void colm_cst_tree_collect_simple_filtered( program_t *prg, tree_t **sp,
        str_collect_t *collect, tree_t *tree, int trim,
        const char * const *hidden_prefixes )
{
    struct cst_filtered_ctx ctx;

    (void)sp;
    (void)trim;

    ctx.prg = prg;
    ctx.collect = collect;
    ctx.hidden_prefixes = hidden_prefixes;
    ctx.show_list = 0;
    memset( ctx.last, 0, sizeof(ctx.last) );
    cst_filtered_node( &ctx, tree, 0, true, true );
}

void colm_cst_tree_collect_simple_show( program_t *prg, tree_t **sp,
        str_collect_t *collect, tree_t *tree, int trim,
        const char *show_list )
{
    struct cst_filtered_ctx ctx;

    (void)sp;
    (void)trim;

    ctx.prg = prg;
    ctx.collect = collect;
    ctx.hidden_prefixes = 0;
    ctx.show_list = show_list;
    memset( ctx.last, 0, sizeof(ctx.last) );
    cst_filtered_node( &ctx, tree, 0, true, true );
}

