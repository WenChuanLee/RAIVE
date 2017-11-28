#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "ggc.h"

#include "tree.h"
#include "basic-block.h"
#include "langhooks.h"
#include "cgraph.h"
#include "gimple.h"
#include "tree-pass.h"
#include "toplev.h"
#include "tree-iterator.h"
#include "real.h"
#include "tree-flow.h"
#include "timevar.h"
#include "tree-pretty-print.h"
#include "gimple-pretty-print.h"
#include "c-family/c-common.h"
#include "diagnostic-core.h"
#include "diagnostic.h"
#include "lineage.h"

/* ------------------------------------------------------------------------ */
//#define LINEAGE_RAND_ROUND
//#define LINEAGE_RAND_LAST_BIT	0
#define LINEAGE_LOG

/* -----------------------CONSTANT VALUES---------------------------------- */
#define LINEAGE_ID_LEN          128
#define LINEAGE_DOUBLE_TYPE     1
#define LINEAGE_FLOAT_TYPE      2
#define LINEAGE_INTEGER_TYPE    3

#define BINOP_FAST_CHECK_BUFFER_SIZE      1024*1024*8
#define EXP_THRESHOLD							40 
#define EXP_THRESHOLD_LARGE               (EXP_THRESHOLD * 0x10000000000000L)
#define EXP_CONSTANT_LARGE                ((EXP_THRESHOLD+1) * 0x10000000000000L)
#define EXP_CONSTANT_ONE				  0x10000000000000L
#define EXP_MASK_LARGE                    0x7FF0000000000000L

//#define NORMAL_VEC
/* -----------------------OPTIMIZTION OPTIONS------------------------------ */

/* Enabled (Optmize): check before making the function call.
 * Otherwise: always make the function call, which can be used to count the numbers */
/* #define CHECK_BEFORE_CALL */

/* Enabled (Normal mode): do the instrumentation.
 * Otherwise (Performance tuning): Instead of generateing actual function calls,
 * only emit a NOP. */
#define ENABLE_COMPUTATION

/* Enabled (Optmize): do not pass description msgs when making the function call.
 * Otherwise: descriptions may induce overhead */
/* #define NO_DESC */

/* #define RETURN_CHANGED_P */

#define TYPE_BASED

/* LINEAGE_P means hashing slices. */
/* #define LINEAGE_P */

/* CKP means doing the global hashing version, which will not update the taint. */
/* We use CKP as the fast predictor impl which calls helper function only at predicates
 * and subtractions/additions. */
/* #define CKP */

/* CKP_EXPLICIT_CALL: if defined, generate explicit function calls to ckp_{i, d, b}.
 * Otherwise, generate inline version by updating p_current.
 */
/* define CKP_EXPLICIT_CALL */

/* #define BINOP_FAST_CHECK_INLINE_BUFFER */

/* #define FORTRAN */

#undef LOCAL_STATIC

#define PRE_ALLOCATION

/* #define ORDER_STATS */

/* #define CHECK_BEFORE_WRITE_SHADOW */

/* #define INLINE_ASSIGNMENT */

/* Doesn't work: #define TESTING_INLINE */

/* -----------------------HELPER MACROS------------------------------------ */

#define ID_PTR_NAME(decl) __extension__ \
	({const char *__id_ptr; \
	 if (!decl || !DECL_P (decl)) \
	 { \
	 __id_ptr = "<unnamed>"; \
	 } \
	 else if (TREE_CODE (decl) == INDIRECT_REF) \
	 { \
	 __id_ptr = "indirect"; \
	 } \
	 else if (DECL_NAME (decl)) \
	 { \
	 __id_ptr = IDENTIFIER_POINTER (DECL_NAME (decl)); \
	 } \
	 else  \
	 { \
	 char *__id_ptr2 = (char *) alloca (LINEAGE_ID_LEN);  \
	 sprintf (__id_ptr2, "D.%u", DECL_UID (decl));  \
	 __id_ptr = __id_ptr2; \
	 } \
	 __id_ptr; })

#define SHADOW_ID_PREFIX(prefix,id_ptr) __extension__ \
	({  \
	 char __shadow_id[LINEAGE_ID_LEN]; \
	 char *__pc; \
	 strcpy (__shadow_id, prefix);  \
	 strcat (__shadow_id, id_ptr); \
	 while ((__pc = strchr(__shadow_id, '.')) != NULL) \
	 *__pc = '_';  \
	 __shadow_id;  })

#define TYPE_SIZE_INT(decl) (TREE_INT_CST_LOW (TYPE_SIZE (TREE_TYPE (decl))))


typedef struct shadow_hash_elt
{
	tree var;   /* Key */
	tree shadow;  /* Value */
} shadow_hash_elt_t;

enum op_t {
	OP_EQ = 1,
	OP_NE,
	OP_LE,
	OP_GE,
	OP_LT,
	OP_GT,
	OP_SWITCH
};

/* -----------------------LOCAL VARIABLES---------------------------------- */
static int see_main_p = 0;
#ifndef LINEAGE_P
static unsigned ckp_counter = 1;
#endif

/* Mark and return the given tree node to prevent further transforms.  */
static GTY ((param_is (union tree_node))) htab_t marked_decls = NULL;
static GTY ((param_is (union tree_node))) htab_t shadow_trees = NULL;
static GTY ((param_is (gimple))) htab_t marked_stmts = NULL;

/* extern void __lineage_init (void); */
static GTY (()) tree lineage_init_fndecl;

/* extern void __lineage_fini (void); */
static GTY (()) tree lineage_fini_fndecl;

/* extern unsigned __lineage_union_fndecl (unsigned); */
static GTY (()) tree lineage_union_fndecl;

/******************** RAIVE New Design Begin ********************/
/* extern void lineage_acc_err(double, double, double, 
 *				unsigned long, const char *desc) 
 */
static GTY (()) tree lineage_acc_err_fndecl;

/* extern void lineage_large_cancel(double, double, double, 
 *				unsigned long, unsigned long, const char *desc) 
 */
static GTY (()) tree lineage_large_cancel_fndecl;
/* extern void lineage_record_op(const char *desc) 
 */
static GTY (()) tree lineage_record_op_fndecl;

/* extern void lineage_print_value(usigned long int, const char *desc) */
static GTY (()) tree lineage_print_value_fndecl;

/* extern void lineage_print_vector(__m256d *ptr) */
static GTY (()) tree lineage_print_vector_fndecl;
/* 
 * extern int lineage_spawn(int r1, int r2, 
 *				__m256d *vL, __m256d *vR, const char *desc) 
 */
static GTY (()) tree lineage_spawn_fndecl;
/* 
 * extern void lineage_check_equal(__m256d *vec, const char *desc) 
 */
static GTY (()) tree lineage_check_equal_fndecl;
/* 
 * extern void lineage_force_exit(const char *desc) 
 */
static GTY (()) tree lineage_force_exit_fndecl;
/*
 * extern int lineage_check_concore(void *plhs, void *prhs, int type,
 *				int isLast, const char *desc) 
 */
static GTY (()) tree lineage_check_concore_fndecl;
/* 
 * extern void inst_vec_elemcpy(__m256d *vec, int dstIdx, int srcIdx) 
 */
static GTY (()) tree inst_vec_elemcpy_fndecl;
/* 
 * extern void inst_check_nan(__m256d *vec) 
 */
static GTY (()) tree inst_vec_check_nan_fndecl;
/* 
 * extern void inst_check_debug(__m256d *vec) 
 */
static GTY (()) tree inst_vec_debug_fndecl;
/*
 * extern void lineage_random_rounding_mode();
 */
static GTY (()) tree lineage_random_rounding_mode_fndecl;
/*
 * extern double lineage_random_last_bit(double);
 */
static GTY (()) tree lineage_random_last_bit_fndecl;

/******************** RAIVE New Design End   ********************/

/* -----------------------FUNCTION PROTOTYPES------------------------------ */
static tree lineage_decls_mark (tree t);
static int lineage_decls_marked_p (tree t);
static gimple lineage_stmts_mark (gimple gs);
static int lineage_stmts_marked_p (gimple gs);

/* Addressable variables instrumentation.  */
static void lineage_xform_fn (gimple_seq, tree);
static tree lineage_xfn_xform_fn (gimple_stmt_iterator *, bool *, struct walk_stmt_info *);
static tree lineage_get_addr (gimple_seq *, tree, location_t);
static tree detail_varname_tree (tree, location_t) __attribute__ ((unused));
static const char *detail_component_info (const tree, location_t) __attribute__ ((unused));
static const char *detail_decl_info (const tree, location_t) __attribute__ ((unused));

extern void dump_tree_ssa (FILE *);

/* -----------------------FUNCTION DEFINITIONS----------------------------- */
/* Some generally helpful functions for instrumentation.  */

/* Build a reference to a literal string.  */
static tree
lineage_build_string (const char *string)
{
	size_t len = strlen (string);
	tree result = lineage_decls_mark (build_string (len + 1, string));

	TREE_TYPE (result) = build_array_type
		(char_type_node, build_index_type (build_int_cst (NULL_TREE, len)));
	TREE_CONSTANT (result) = 1;
	TREE_READONLY (result) = 1;
	TREE_STATIC (result) = 1;

	result = build1 (ADDR_EXPR, build_pointer_type (char_type_node), result);

	return lineage_decls_mark (result);
}


/* Create a properly typed STRING_CST node that describes the given
   declaration.  It will be used as an argument for __mf_register().
   Try to construct a helpful string, including file/function/variable
   name.  */
static tree
detail_varname_tree (tree decl, location_t location)
{
	static pretty_printer buf_rec;
	static int initialized = 0;
	pretty_printer *buf = & buf_rec;
	const char *buf_contents;
	tree result;

	gcc_assert (decl);

	if (!initialized)
	{
		pp_construct (buf, /* prefix */ NULL, /* line-width */ 0);
		initialized = 1;
	}
	pp_clear_output_area (buf);

	/* Add FILENAME[:LINENUMBER[:COLUMNNUMBER]].  */
	{
		expanded_location xloc = expand_location (location);
		const char *sourcefile;
		unsigned sourceline = xloc.line;
		unsigned sourcecolumn = 0;
		sourcecolumn = xloc.column;
		sourcefile = xloc.file;
		if (sourcefile == NULL && current_function_decl != NULL_TREE)
			sourcefile = DECL_SOURCE_FILE (current_function_decl);
		if (sourcefile == NULL)
			sourcefile = "<unknown file>";

		pp_string (buf, sourcefile);

		if (sourceline != 0)
		{
			pp_string (buf, ":");
			pp_decimal_int (buf, sourceline);

			if (sourcecolumn != 0)
			{
				pp_string (buf, ":");
				pp_decimal_int (buf, sourcecolumn);
			}
		}
	}

	if (current_function_decl != NULL_TREE)
	{
		/* Add (FUNCTION) */
		pp_string (buf, " (");
		{
			const char *funcname = NULL;
			if (DECL_NAME (current_function_decl))
				funcname = lang_hooks.decl_printable_name (current_function_decl, 1);
			if (funcname == NULL)
				funcname = "anonymous fn";

			pp_string (buf, funcname);
		}
		pp_string (buf, ") ");
	}
	else
		pp_string (buf, " ");

	/* Add <variable-declaration>, possibly demangled.  */
	{
		const char *declname = NULL;

		if (DECL_NAME (decl) != NULL)
		{
			if (declname == NULL)
				declname = lang_hooks.decl_printable_name (decl, 3);
		}
		if (declname == NULL)
			declname = "<unnamed>";

		pp_string (buf, declname);
	}

	/* Return the lot as a new STRING_CST.  */
	buf_contents = pp_base_formatted_text (buf);
	result = lineage_build_string (buf_contents);
	pp_clear_output_area (buf);

	return result;
}

static const char *
detail_decl_info (const tree decl, location_t location)
{
	static pretty_printer buf_rec;
	static int initialized = 0;
	pretty_printer *buf = & buf_rec;
	const char *buf_contents;

	gcc_assert (decl);

	if (!initialized)
	{
		pp_construct (buf, /* prefix */ NULL, /* line-width */ 0);
		initialized = 1;
	}
	pp_clear_output_area (buf);

	/* Add FILENAME[:LINENUMBER[:COLUMNNUMBER]].  */
	{
		expanded_location xloc = expand_location (location);
		const char *sourcefile;
		unsigned sourceline = xloc.line;
		unsigned sourcecolumn = 0;
		sourcecolumn = xloc.column;
		sourcefile = xloc.file;
		if (sourcefile == NULL && current_function_decl != NULL_TREE)
			sourcefile = DECL_SOURCE_FILE (current_function_decl);
		if (sourcefile == NULL)
			sourcefile = "<unknown file>";

		pp_string (buf, sourcefile);

		if (sourceline != 0)
		{
			pp_string (buf, ":");
			pp_decimal_int (buf, sourceline);

			if (sourcecolumn != 0)
			{
				pp_string (buf, ":");
				pp_decimal_int (buf, sourcecolumn);
			}
		}
	}

	pp_string (buf, " ");

	dump_generic_node (buf, decl, 0, TDF_DIAGNOSTIC, false);
	buf_contents = pp_base_formatted_text (buf);
	pp_clear_output_area (buf);

	return buf_contents;
}

static const char *
detail_component_info (const tree decl, location_t location)
{
	static pretty_printer buf_rec;
	static int initialized = 0;
	pretty_printer *buf = & buf_rec;
	const char *buf_contents;

	gcc_assert (decl);

	if (!initialized)
	{
		pp_construct (buf, /* prefix */ NULL, /* line-width */ 0);
		initialized = 1;
	}
	pp_clear_output_area (buf);

	/* Add FILENAME[:LINENUMBER[:COLUMNNUMBER]].  */
	{
		expanded_location xloc = expand_location (location);
		const char *sourcefile;
		unsigned sourceline = xloc.line;
		unsigned sourcecolumn = 0;
		sourcecolumn = xloc.column;
		sourcefile = xloc.file;
		if (sourcefile == NULL && current_function_decl != NULL_TREE)
			sourcefile = DECL_SOURCE_FILE (current_function_decl);
		if (sourcefile == NULL)
			sourcefile = "<unknown file>";

		pp_string (buf, sourcefile);

		if (sourceline != 0)
		{
			pp_string (buf, ":");
			pp_decimal_int (buf, sourceline);

			if (sourcecolumn != 0)
			{
				pp_string (buf, ":");
				pp_decimal_int (buf, sourcecolumn);
			}
		}
	}

	pp_string (buf, " ");

	dump_generic_node (buf, decl, 0, TDF_DIAGNOSTIC, false);
	buf_contents = pp_base_formatted_text (buf);
	pp_clear_output_area (buf);

	return buf_contents;
}


/* Mark the given tree node T for variable/parameters decls */
static tree
lineage_decls_mark (tree t)
{
	void **slot;

	if (marked_decls == NULL)
		marked_decls = htab_create_ggc(31, htab_hash_pointer, 
			htab_eq_pointer, NULL);

	slot = htab_find_slot (marked_decls, t, INSERT);
	*slot = t;
	return t;
}

/* Check whether the given tree node T has been marked */

static int
lineage_decls_marked_p (tree t)
{
	void *entry;

	if (marked_decls == NULL)
		return 0;

	entry = htab_find (marked_decls, t);
	return (entry != NULL);
}

/* Mark the given gimple stmt GS */

static gimple
lineage_stmts_mark (gimple gs)  
{
	void **slot;

	if (marked_stmts == NULL)
		marked_stmts = 
			htab_create_ggc (31, htab_hash_pointer, htab_eq_pointer, NULL);

	slot = htab_find_slot (marked_stmts, gs, INSERT);
	*slot = gs;
	return gs;
}

/* Check whether the given gimple stmt GS has been marked */
static int
lineage_stmts_marked_p (gimple gs)
{
	void *entry;

	if (marked_stmts == NULL)
		return 0;

	entry = htab_find (marked_stmts, gs);
	return (entry != NULL);
}

/* 
 * Helper for lineage_init: construct a decl with the given category,
 * name, and type, mark it an external reference, and pushdecl it.
 */
static inline tree
lineage_make_builtin (enum tree_code category, const char *name, tree type)
{
	tree decl = build_decl(UNKNOWN_LOCATION, category, 
		get_identifier(name), type);
	
	TREE_PUBLIC (decl) = 1;
	DECL_EXTERNAL (decl) = 1;
	lang_hooks.decls.pushdecl (decl);
	/* The decl was declared by the compiler.  */
	DECL_ARTIFICIAL (decl) = 1;
	/* And we don't want debug info for it.  */
	DECL_IGNORED_P (decl) = 1;
	return decl;
}

#define build_function_type_0(rtype)                \
	build_function_type (rtype, void_list_node)

#define build_function_type_1(rtype, arg1)          \
	build_function_type (rtype, tree_cons (0, arg1, void_list_node))

#define build_function_type_2(rtype, arg1, arg2) \
	build_function_type (rtype, \
			tree_cons (0, arg1, \
				tree_cons (0, arg2, \
					void_list_node)))

#define build_function_type_3(rtype, arg1, arg2, arg3) \
	build_function_type (rtype, \
			tree_cons (0, arg1, \
				tree_cons (0, arg2, \
					tree_cons (0, arg3, \
						void_list_node))))

#define build_function_type_4(rtype, arg1, arg2, arg3, arg4) \
	build_function_type (rtype, \
			tree_cons (0, arg1,     \
				tree_cons (0, arg2, \
					tree_cons (0, arg3,     \
						tree_cons (0, arg4, \
							void_list_node)))))

#define build_function_type_5(rtype, arg1, arg2, arg3, arg4, arg5) \
	build_function_type (rtype, \
			tree_cons (0, arg1, \
				tree_cons (0, arg2, \
					tree_cons (0, arg3, \
						tree_cons (0, arg4, \
							tree_cons (0, arg5, \
								void_list_node))))))

#define build_function_type_6(rtype, arg1, arg2, arg3, arg4, arg5, arg6) \
	build_function_type (rtype, \
			tree_cons (0, arg1, \
				tree_cons (0, arg2, \
					tree_cons (0, arg3, \
						tree_cons (0, arg4, \
							tree_cons (0, arg5, \
								tree_cons (0, arg6, \
									void_list_node)))))))

#define build_function_type_7(rtype, arg1, arg2, arg3, arg4, arg5, arg6, arg7) \
	build_function_type (rtype, \
			tree_cons (0, arg1, \
				tree_cons (0, arg2, \
					tree_cons (0, arg3, \
						tree_cons (0, arg4, \
							tree_cons (0, arg5, \
								tree_cons (0, arg6, \
									tree_cons (0, arg7, \
										void_list_node))))))))

#define build_function_type_8(rtype, arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8) \
	build_function_type (rtype, \
			tree_cons (0, arg1, \
				tree_cons (0, arg2, \
					tree_cons (0, arg3, \
						tree_cons (0, arg4, \
							tree_cons (0, arg5, \
								tree_cons (0, arg6, \
									tree_cons (0, arg7, \
										tree_cons (0, arg8, \
											void_list_node)))))))))

/* Initialize the global tree nodes that correspond to mf-runtime.h
   declarations.  */
	void
lineage_init (void)
{
	static bool done = false;
	tree lineage_const_string_type;

	if (done)
		return;
	done = true;

	lineage_const_string_type =
		build_pointer_type (build_qualified_type
				(char_type_node, TYPE_QUAL_CONST));

	/* V4DF: vector for 4 double fp */
	{
		/* Moved to tree.c */
		/*    v4df_type_node = build_vector_type (double_type_node, 4); */
	}

	/* V2DF: vector for 2 double fp */
	{
		/* Moved to tree.c */
		/* v2df_type_node = build_vector_type (double_type_node, 2); */
	}
	
	{
		tree lineage_init_fntype = 
			build_function_type_1 (void_type_node, integer_type_node);

		lineage_init_fndecl =
			lineage_make_builtin (FUNCTION_DECL, "lineage_init",
					lineage_init_fntype);
	}

	{
		tree lineage_fini_fntype = 
			build_function_type_1 (void_type_node, void_type_node);

		lineage_fini_fndecl =
			lineage_make_builtin (FUNCTION_DECL, "lineage_fini",
					lineage_fini_fntype);
	}

	/******************** RAIVE New Design Begin ********************/
	
	{
		tree lineage_acc_err_fntype;

		lineage_acc_err_fntype = 
			build_function_type_5(void_type_node,
				double_type_node, double_type_node, double_type_node,
				long_unsigned_type_node, lineage_const_string_type);

		lineage_acc_err_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_acc_err",
				lineage_acc_err_fntype);
	}
	
	{
		tree lineage_large_cancel_fntype;

		lineage_large_cancel_fntype = 
			build_function_type_6(void_type_node,
				double_type_node, double_type_node, double_type_node,
				long_unsigned_type_node, long_unsigned_type_node, 
				lineage_const_string_type);

		lineage_large_cancel_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_large_cancel",
				lineage_large_cancel_fntype);
	}
	
	{
		tree lineage_record_op_fntype;

		lineage_record_op_fntype = 
			build_function_type_1(void_type_node,
				lineage_const_string_type);

		lineage_record_op_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_record_op",
				lineage_record_op_fntype);
	}

	{
		tree lineage_print_value_fntype;

		lineage_print_value_fntype = 
			build_function_type_2(void_type_node,
				long_long_unsigned_type_node,
				lineage_const_string_type);

		lineage_print_value_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_print_value",
				lineage_print_value_fntype);
	}
	
	{
		tree lineage_print_vector_fntype;

		lineage_print_vector_fntype = 
			build_function_type_1(void_type_node,
				build_pointer_type(v4df_type_node));

		lineage_print_vector_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_print_vector",
				lineage_print_vector_fntype);
	}

	{
		tree lineage_spawn_fntype;

		lineage_spawn_fntype = 
			build_function_type_6(integer_type_node, integer_type_node,
				integer_type_node, integer_type_node,
				build_pointer_type(v4df_type_node), 
				build_pointer_type(v4df_type_node),
				lineage_const_string_type);

		lineage_spawn_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_spawn",
				lineage_spawn_fntype);
	}

	{
		tree lineage_check_equal_fntype;

		lineage_check_equal_fntype = 
			build_function_type_2(void_type_node, 
				build_pointer_type(v4df_type_node),
				lineage_const_string_type);

		lineage_check_equal_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_check_equal",
				lineage_check_equal_fntype);
	}

	{
		tree lineage_force_exit_fntype;

		lineage_force_exit_fntype = 
			build_function_type_1(void_type_node, lineage_const_string_type);

		lineage_force_exit_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_force_exit",
				lineage_force_exit_fntype);
	}
	
	{
		tree lineage_check_concore_fntype;
		
		lineage_check_concore_fntype = 
			build_function_type_5(integer_type_node, 
				void_type_node, void_type_node, integer_type_node,
				integer_type_node, lineage_const_string_type);
		
		lineage_check_concore_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_check_concore",
				lineage_check_concore_fntype);

	}

	{
		tree inst_vec_elemcpy_fntype;

		inst_vec_elemcpy_fntype = 
			build_function_type_3(void_type_node, 
				build_pointer_type(v4df_type_node), integer_type_node, 
				integer_type_node);

		inst_vec_elemcpy_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "inst_vec_elemcpy",
				inst_vec_elemcpy_fntype);
	}
	
	{
		tree inst_vec_check_nan_fntype;

		inst_vec_check_nan_fntype = 
			build_function_type_1(void_type_node, 
				build_pointer_type(v4df_type_node));

		inst_vec_check_nan_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "inst_vec_check_nan",
				inst_vec_check_nan_fntype);
	}
	
	{
		tree inst_vec_debug_fntype;

		inst_vec_debug_fntype = 
			build_function_type_2(void_type_node, 
				build_pointer_type(v4df_type_node),
				lineage_const_string_type);

		inst_vec_debug_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "inst_vec_debug",
				inst_vec_debug_fntype);
	}
	
	{
		tree lineage_random_rounding_mode_fntype;

		lineage_random_rounding_mode_fntype = 
			build_function_type_0(void_type_node);

		lineage_random_rounding_mode_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_random_rounding_mode",
				lineage_random_rounding_mode_fntype);
	}
	
	{
		tree lineage_random_last_bit_fntype;

		lineage_random_last_bit_fntype = 
			build_function_type_1(double_type_node, double_type_node);

		lineage_random_last_bit_fndecl = 
			lineage_make_builtin(FUNCTION_DECL, "lineage_random_last_bit",
				lineage_random_last_bit_fntype);
	}
	/******************** RAIVE New Design End   ********************/
}


static tree
lineage_get_addr_plus_8 (gimple_seq *seq_p, tree addr, location_t location)
{
	tree addr_op1_0, addr_op1_8;
	gimple_seq seq2 = NULL;
	tree t;
	gimple g;

	/* addr_op1_0 = (long unsigned) addr */
	addr_op1_0 = lineage_decls_mark (
			create_tmp_var (long_unsigned_type_node, SHADOW_ID_PREFIX("__addr_", "imag")));
	t = fold_build1 (CONVERT_EXPR, long_unsigned_type_node, addr);
	gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
	g = gimple_build_assign (addr_op1_0, t);
	gimple_set_location (g, location);
	gimple_seq_add_stmt (&seq2, g);

	/* addr_op1_8 = addr_op1_0 + 8 */
	addr_op1_8 = lineage_decls_mark (
			create_tmp_var (long_unsigned_type_node, SHADOW_ID_PREFIX("__addr_", "imag")));
	t = fold_build2 (PLUS_EXPR, long_unsigned_type_node, addr_op1_0, build_int_cst (NULL_TREE, 8));
	g = gimple_build_assign (addr_op1_8, t);
	gimple_set_location (g, location);
	gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);

	gimple_seq_add_stmt (&seq2, g);

	gimple_seq_add_seq (seq_p, seq2);

	return addr_op1_8;
}


/* May return -1 for non-addressable varialbes. */
static tree
lineage_get_imag (gimple_seq *seq_p, tree decl, tree addr, location_t location)
{
	tree tree_imag;

	/* Non-addressable? */
	if (!addr)
	{
		tree_imag = build_int_cst (long_unsigned_type_node, -1);
	}
	else
	{
		tree addr_op1_8;

		addr_op1_8 = lineage_get_addr_plus_8 (seq_p, addr, location);
		tree_imag = lineage_gen_get_shadow (seq_p, decl, addr_op1_8, location);
	}

	return tree_imag;
}


#undef build_function_type_0
#undef build_function_type_1
#undef build_function_type_2
#undef build_function_type_3
#undef build_function_type_4
#undef build_function_type_5
#undef build_function_type_6
#undef build_function_type_7
#undef build_function_type_8


/* This struct is passed between lineage_xform_decls to store state needed
   during the traversal searching for objects that have their
   addresses taken.  */
struct lineage_xform_decls_data
{
	tree param_decls;
};

static gimple top_bind;
static gimple_seq allocate_seq;

/* Process every variable and every statement mentioned in BIND_EXPRs.  */
static tree
lineage_mark_seq (gimple_stmt_iterator *gsi,
		bool *handled_operands_p ATTRIBUTE_UNUSED,
		struct walk_stmt_info *wi)
{
	gimple stmt = gsi_stmt (*gsi);
	location_t location = *(location_t *) (wi->info);

	lineage_stmts_mark (stmt);
	gimple_set_location (stmt, location);

#if 0
	debug_gimple_stmt (stmt);
#endif

	return NULL_TREE;
}

static void lineage_dump_op_name(tree op)
{
	if (TREE_CODE(op) == MEM_REF)
		op = TREE_OPERAND(op, 0);

	if (DECL_NAME(op)) {
		printf("%s\n", get_name(op));
	} else {
		printf("D.%u\n", DECL_UID(op));
	}
}

static void lineage_dump_stmt(gimple gs)
{
	int i;

	print_gimple_stmt (stdout, gs, 0, 0);

	for (i=0; i<gimple_num_ops(gs); i++) {
		tree op = gimple_op(gs, i);

		if (op && !CONSTANT_CLASS_P(op) && TREE_CODE(op) != CONSTRUCTOR) {
			bool isRef = (TREE_CODE(op) == MEM_REF) ||
				(TREE_CODE(op) == ARRAY_REF);

			if (isRef){
				printf("[BEF:0x%x ", op);
				op = TREE_OPERAND(op, 0);
				printf("AFT:0x%x]", op);
			}
			printf("[op%d][REF:%d][DECL_ARTIFICIAL:%d]\n", 
				i, isRef, DECL_ARTIFICIAL(op));
			
			lineage_dump_op_name(op);
		}
	}
}
/*
 * Get the last variable which defined current variable
 * before current stmt.
 * 
 * On return, just return the original use variable. If it is
 * a gimple call, just return NULL.
 */
static tree lineage_get_last_def(gimple_stmt_iterator *gsi, tree var)
{
	/* Find out by the rule of reaching definition. */
	struct gimple_seq_node_d *pSeq;

	for (pSeq=gsi->ptr->prev; pSeq; pSeq=pSeq->prev) {
		gimple stmt = pSeq->stmt;

		switch (gimple_code(stmt)) {
			case GIMPLE_ASSIGN:
			{
				tree rhs = gimple_assign_rhs1(stmt);
				tree op0 = gimple_assign_lhs(stmt);

				if (op0 == var)
					return rhs;

				break;
			}
			case GIMPLE_CALL:
			{
				if (gimple_call_lhs(stmt) == var)
					return NULL;

				break;
			}
		}
	}

	return NULL;
}


/* 
 * Get the user declared variable from gcc declared variable. 
 * For example, we want to get the tree node of a variable,
 * say x, gcc may declare a duplicate operand, say x.12, and
 * assign x's value to x.12. In order to modify the value of
 * original operand, we need to get it.
 *
 * Here we use recursive to find it in backward manner.
 */
static tree lineage_get_decl_var_rec(
	struct gimple_seq_node_d *pSeq, tree var)
{
	if (!pSeq)
		return NULL;

	gimple stmt = pSeq->stmt;
	
	if (gimple_code(stmt) == GIMPLE_ASSIGN) {
		int i;

		for (i=1; i<gimple_num_ops(stmt); i++) {
			tree rhs = gimple_op(stmt, i);

			if (rhs) {
				tree prhs = rhs;
				/* 
				 * For the MEM_REF operands, we have to take the outer 
				 * dereference mark out, otherwise we will get wrong result.
				 */
				if (TREE_CODE(prhs) == MEM_REF || TREE_CODE(prhs) == ARRAY_REF)
					prhs = TREE_OPERAND(prhs, 0);

				/* If current lhs is what we expected previously */
				if (gimple_assign_lhs(stmt) == var)	{
					/* 
					 * Two situations 
					 * 1. It is declared by user
					 * 2. It is declared by gcc but it is a pointer to a
					 *	  user-declared variable, then we can still modify 
					 *	  the right address through this variable.
					 */
					if (!DECL_ARTIFICIAL(prhs) || (prhs != rhs)) {
						return unshare_expr(rhs);
					} else {
						if (prhs = lineage_get_decl_var_rec(pSeq->prev, prhs))
							return prhs;
					}
				} else {
					return lineage_get_decl_var_rec(pSeq->prev, var);
				}
			}
		}
	}

	return NULL;
}

/*
 * For checking patched number, patchL must <= patchR, else
 * we will have error result.
 */
static void
lineage_assert(gimple_seq *seq, location_t location, 
	enum tree_code tc, tree lhs, tree rhs)
{
	tree label_error, label_good;
	gimple g;

	label_error = create_artificial_label(location);
	label_good = create_artificial_label(location);
	
	gimple_seq_add_stmt (seq, gimple_build_cond 
		(tc, lhs, rhs, label_good, label_error));

	gimple_seq_add_stmt (seq, gimple_build_label(label_error));
	
	g = gimple_build_call(lineage_force_exit_fndecl, 1, 
		lineage_build_string(detail_decl_info(lhs, location)));

	gimple_set_location(g, location);
	gimple_seq_add_stmt(seq, g);
	
	gimple_seq_add_stmt(seq, gimple_build_label(label_good));
}
static void
lineage_inline_vec_debug(gimple_seq *seq0_p, gimple_seq *seq2_p, 
	location_t location, enum tree_code op_code ATTRIBUTE_UNUSED, 
	tree op0, tree op1, tree op2)
{
	gimple_seq seq2 = NULL;
	tree t;
	gimple g;

	if (TYPE_SIZE_INT (op0) < 256)
		return;

	t = build1 (ADDR_EXPR,
			build_pointer_type (v4df_type_node), unshare_expr (op0));
	gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
	
	g = gimple_build_call(inst_vec_debug_fndecl, 2, t, 
		lineage_build_string(detail_decl_info(op0, location)));

	gimple_set_location(g, location);
	gimple_seq_add_stmt(seq2, g);

	{
		gimple g;
		g = lineage_stmts_mark (gimple_build_bind (NULL, seq2, NULL));
		gimple_seq_add_stmt (seq2_p, g);
	}

	/* mark all */
	{
		struct walk_stmt_info wi;

		/* Mark all the stmts in the seq */
		memset (&wi, 0, sizeof (wi));
		wi.info = &location;
		walk_gimple_seq (*seq2_p, lineage_mark_seq, NULL, &wi);
	}  
}

/*
 * For vectorization operation plus and minus only.
 * Currently, we only handle operands with size 256.
 *
 * Parm Description:
 *
 * seq0_p: sequences before current statement
 * seq2_p: sequences after current statement
 * location:
 */
static void
lineage_inline_plus_minus(gimple_seq *seq0_p, gimple_seq *seq2_p, 
	location_t location, enum tree_code op_code ATTRIBUTE_UNUSED, 
	tree op0, tree op1, tree op2)
{
	gimple_seq seq0 = NULL;
	gimple_seq seq2 = NULL;

	gimple binop_fncall;
	binop_fncall = gimple_build_nop ();

	switch (TYPE_SIZE_INT (op0)) {
		case 256:
		{
			gimple g;
			tree op1_copy;
			/* 
			 * p1 may change for such operation: a = a + b 
			 * Thus, we need an original copy of op1 and do
			 * it before operation.
			 */
			op1_copy = lineage_decls_mark(
					create_tmp_var(v4df_type_node, 
						SHADOW_ID_PREFIX("__op1_", "copy")));

			g = lineage_stmts_mark(gimple_build_assign(op1_copy, 
						unshare_expr(op1)));

			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq0, g);

			/* Inline version */
			tree t;
			tree vop0_ptr, vop1_ptr, vop2_ptr;
			tree op0_ptr, op1_ptr, op2_ptr;
			tree delta, delta2;
			tree exp0, exp1, exp2;
			tree label_p1, label_check_and_set_done;
			tree patch_d1, patch_ptr;
			tree patch, patch_neg;
			tree vpatch;

			/* op0_ptr */
			vop0_ptr = lineage_decls_mark (
					create_tmp_var (build_pointer_type(v4df_type_node), 
						SHADOW_ID_PREFIX("__vop0_", "ptr")));
			op0_ptr = lineage_decls_mark (
					create_tmp_var (double_ptr_type_node, 
						SHADOW_ID_PREFIX("__op0_", "ptr")));
			
			t = build1 (ADDR_EXPR,
					build_pointer_type (v4df_type_node), unshare_expr (op0));
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign (vop0_ptr, t);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);
			
			t = build1 (CONVERT_EXPR, double_ptr_type_node, vop0_ptr);
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign(op0_ptr, t);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq2, g);

			/* op1_ptr */
			vop1_ptr = lineage_decls_mark (
					create_tmp_var (build_pointer_type(v4df_type_node), 
						SHADOW_ID_PREFIX("__vop1_", "ptr")));
			op1_ptr = lineage_decls_mark (
					create_tmp_var (double_ptr_type_node, 
						SHADOW_ID_PREFIX("__op1_", "ptr")));
			
			t = build1 (ADDR_EXPR,
					build_pointer_type (v4df_type_node), op1_copy);
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign (vop1_ptr, t);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);
			
			t = build1 (CONVERT_EXPR, double_ptr_type_node, vop1_ptr);
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign(op1_ptr, t);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq2, g);
			/* op2_ptr */
			/*op2_ptr = build1 (ADDR_EXPR,
					build_pointer_type (v4df_type_node), unshare_expr(op2));*/
			/* 
			 * Get exponent from:
			 *
			 * 1. result (i.e. exp0) and
			 * 2. op1 (i.e. exp1) 
			 */

			/* exp0 */
			exp0 = lineage_decls_mark (
					create_tmp_var (long_unsigned_type_node, 
						SHADOW_ID_PREFIX("__op0_", "exp0")));

			t = build1 (INDIRECT_REF, long_unsigned_type_node, op0_ptr);
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign (exp0, t);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);

			t = fold_build2 (BIT_AND_EXPR, long_unsigned_type_node, exp0,
					build_int_cst (long_unsigned_type_node, EXP_MASK_LARGE));
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign (exp0, t);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);
			
			/* exp1 */
			exp1 = lineage_decls_mark(
					create_tmp_var(long_unsigned_type_node, 
						SHADOW_ID_PREFIX("__op1_", "exp1")));

			t = build1 (INDIRECT_REF, long_unsigned_type_node, op1_ptr);
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign (exp1, t);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);

			t = fold_build2 (BIT_AND_EXPR, long_unsigned_type_node, exp1,
					build_int_cst (long_unsigned_type_node, EXP_MASK_LARGE));
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign (exp1, t);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);
			
			/* exp2 */
			/*exp2 = lineage_decls_mark(
					create_tmp_var(long_unsigned_type_node, 
						SHADOW_ID_PREFIX("__op2_", "exp2")));

			t = build1 (INDIRECT_REF, long_unsigned_type_node, op2_ptr);
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign (exp2, t);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);

			t = fold_build2 (BIT_AND_EXPR, long_unsigned_type_node, exp2,
					build_int_cst (long_unsigned_type_node, EXP_MASK_LARGE));
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign (exp2, t);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);*/
			/* delta = op1_exp - op0_exp; */
			{
				delta = create_tmp_var (long_integer_type_node, 
						SHADOW_ID_PREFIX("__exp_", "delta"));

				t = fold_build2 (MINUS_EXPR, long_unsigned_type_node, exp1, exp0);
				gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign (delta, t);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);
			}
			
			/* delta2 = op2_exp - op0_exp; */
			/*{
				delta2 = create_tmp_var (long_integer_type_node, 
						SHADOW_ID_PREFIX("__exp_", "delta2"));

				t = fold_build2 (MINUS_EXPR, long_unsigned_type_node, exp2, exp0);
				gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign (delta2, t);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);
			}*/

			/* delta = max(delta, delta2) */
			{
			/*	label_p1 = create_artificial_label (location);
				label_check_and_set_done = create_artificial_label (location);
				
				gimple_seq_add_stmt (&seq2,	gimple_build_cond 
						(GT_EXPR, delta2, delta,
						 label_p1, label_check_and_set_done));
				gimple_seq_add_stmt (&seq2, gimple_build_label (label_p1));
				
				g = gimple_build_assign (delta, delta2);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);
				
				g = gimple_build_assign (exp1, exp2);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);
					
				gimple_seq_add_stmt (&seq2, gimple_build_label 
						(label_check_and_set_done));
			*/}

			/* Main comparison */

			/* if (delta > EXP_THRESHOLD_LARGE) */

			{
				label_p1 = create_artificial_label (location);
				label_check_and_set_done = create_artificial_label (location);

				gimple_seq_add_stmt (&seq2,	gimple_build_cond 
						(GT_EXPR, delta, build_int_cst 
						 (long_unsigned_type_node, EXP_THRESHOLD_LARGE),
						 label_p1, label_check_and_set_done));

				gimple_seq_add_stmt (&seq2, gimple_build_label (label_p1));
#if 0				
				g = gimple_build_call(lineage_print_value_fndecl, 2, delta,
					lineage_build_string(
					detail_decl_info(unshare_expr(op0), location)));
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);
#endif
				patch_d1 = create_tmp_var (long_unsigned_type_node, 
						SHADOW_ID_PREFIX("__op1_", "patch"));

				t = fold_build2 (MINUS_EXPR, long_unsigned_type_node, 
						exp1, build_int_cst (long_unsigned_type_node, 
						EXP_CONSTANT_LARGE));

				gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign (patch_d1, t);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);

				t = fold_build2 (BIT_AND_EXPR, long_unsigned_type_node, 
						patch_d1, build_int_cst (long_unsigned_type_node, 
						EXP_MASK_LARGE));

				gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign (patch_d1, t);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);

				patch_ptr = create_tmp_var (double_ptr_type_node, 
						SHADOW_ID_PREFIX("__op1_", "patch_ptr"));

				t = fold_build1 (CONVERT_EXPR, double_ptr_type_node, 
						build1 (ADDR_EXPR, build_pointer_type 
						(long_unsigned_type_node), patch_d1));

				gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign (patch_ptr, t);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);

				patch = create_tmp_var (double_type_node,
						SHADOW_ID_PREFIX("__op0_", "patch"));

				t = build1 (INDIRECT_REF, double_type_node, patch_ptr);
				gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign (patch, t);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);

				patch_neg = create_tmp_var (double_type_node,
						SHADOW_ID_PREFIX("__op0_", "patch_neg"));

				t = build1 (NEGATE_EXPR, double_type_node, patch);
				gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign (patch_neg, t);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);

#if 0 
				/* For debugging only */
				lineage_assert(&seq2, location, LE_EXPR,
					patch_neg, patch);
#endif
				vpatch = create_tmp_var (v4df_type_node,
						SHADOW_ID_PREFIX("__op0_", "vpatch"));

				/* NOTE: we cannot call mm(256)_set_pd for Fortran programs. Since 
				 * it is a inline function in the C header.  */
				{
					tree vectype = v4df_type_node;
					int nunits = TYPE_VECTOR_SUBPARTS (vectype);
					VEC(constructor_elt, gc) *v = NULL;

					v = VEC_alloc (constructor_elt, gc, nunits);
					CONSTRUCTOR_APPEND_ELT (v, NULL_TREE, patch_neg);
					CONSTRUCTOR_APPEND_ELT (v, NULL_TREE, patch);
					CONSTRUCTOR_APPEND_ELT (v, NULL_TREE, 
							build_real (double_type_node, dconst0));
					CONSTRUCTOR_APPEND_ELT (v, NULL_TREE, 
							build_real (double_type_node, dconst0));

					g = gimple_build_assign (vpatch, build_constructor 
							(vectype, v));

					gimple_set_location (g, location);
					gimple_seq_add_stmt (&seq2, g);
				}
				t = fold_build2 (PLUS_EXPR, v4df_type_node,
						op0, vpatch);
				gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign (op0, t);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);

				gimple_seq_add_stmt (&seq2, gimple_build_label 
						(label_check_and_set_done));
			}
			 
			break;
		}
		case 64: /* For testing accumulative error only */
		{
			if ((TREE_CODE(TREE_TYPE(op0)) == REAL_TYPE) ||
				(TREE_CODE(TREE_TYPE(op1)) == REAL_TYPE) ||
				(TREE_CODE(TREE_TYPE(op2)) == REAL_TYPE))
			{
				tree op0_ptr, op1_ptr, op2_ptr;
				tree op1_copy;
				tree op0_exp, op1_exp, op2_exp;
				tree t;
				tree delta, delta1, delta2;
				gimple g;

#ifdef LINEAGE_RAND_ROUND	
				/* set random rounding mode */
				g = gimple_build_call(lineage_random_rounding_mode_fndecl, 0);
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq0, g);
#endif
#ifdef LINEAGE_RAND_LAST_BIT	
				/* Add/sub random last bit */
				g = gimple_build_call(lineage_random_last_bit_fndecl, 1,
						unshare_expr(op0));
				gimple_call_set_lhs(g, unshare_expr(op0));
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq2, g);
#endif
#ifdef LINEAGE_LOG
				g = gimple_build_call(lineage_record_op_fndecl, 1,
					lineage_build_string(
						detail_decl_info(unshare_expr(op0), location)));
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq2, g);
				/* 
				 * p1 may change for such operation: a = a + b 
				 * Thus, we need an original copy of op1 and do
				 * it before operation.
				 */
				op1_copy = lineage_decls_mark(
						create_tmp_var(double_type_node, 
							SHADOW_ID_PREFIX("__op1_", "copy")));

				g = lineage_stmts_mark(gimple_build_assign(op1_copy, 
							unshare_expr(op1)));

				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq0, g);
				
				/* op1_ptr */
				op1_ptr = lineage_decls_mark(
							create_tmp_var(
								build_pointer_type(long_unsigned_type_node),
								SHADOW_ID_PREFIX("__op1_", "ptr")));

				t = build1(ADDR_EXPR, double_ptr_type_node, 
						unshare_expr(op1_copy));

				gimplify_expr(&t, &seq0, &seq0, is_gimple_reg_rhs, fb_rvalue);

				t = build1(CONVERT_EXPR, 
						build_pointer_type(long_unsigned_type_node), t);

				g = gimple_build_assign(op1_ptr, t);
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq0, g);
			
				/* op2_ptr */
				op2_ptr = lineage_decls_mark(
							create_tmp_var(
								build_pointer_type(long_unsigned_type_node),
								SHADOW_ID_PREFIX("__op2_", "ptr")));

				t = build1(ADDR_EXPR, double_ptr_type_node, unshare_expr(op2));

				gimplify_expr(&t, &seq0, &seq0, is_gimple_reg_rhs, fb_rvalue);

				t = build1(CONVERT_EXPR, 
						build_pointer_type(long_unsigned_type_node), t);

				g = gimple_build_assign(op2_ptr, t);
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq0, g);

				/* op1_exp */
				op1_exp = lineage_decls_mark(
						create_tmp_var(long_unsigned_type_node, 
							SHADOW_ID_PREFIX("__op1_", "exp")));

				t = build1(INDIRECT_REF, long_unsigned_type_node, op1_ptr);
				gimplify_expr(&t, &seq0, &seq0, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign (op1_exp, t);
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq0, g);

				t = fold_build2 (BIT_AND_EXPR, long_unsigned_type_node, op1_exp,
						build_int_cst(long_unsigned_type_node, EXP_MASK_LARGE));
				gimplify_expr (&t, &seq0, &seq0, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign (op1_exp, t);
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq0, g);

				/* op2_exp */
				op2_exp = lineage_decls_mark(
							create_tmp_var(long_unsigned_type_node, 
							SHADOW_ID_PREFIX("__op2_", "exp")));

				t = build1(INDIRECT_REF, long_unsigned_type_node, op2_ptr);
				gimplify_expr(&t, &seq0, &seq0, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign(op2_exp, t);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq0, g);

				t = fold_build2(BIT_AND_EXPR, long_unsigned_type_node, op2_exp,
						build_int_cst(long_unsigned_type_node, EXP_MASK_LARGE));
				gimplify_expr (&t, &seq0, &seq0, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign(op2_exp, t);
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq0, g);

				/* 
				 * 1. Check for accumulation error:
				 *    Compare the exp between op1 and op2
				 */
				/* delta = op1_exp - op2_exp; */
				{
					tree label_true;
					tree label_false;
					tree label_done;
					
					label_true = create_artificial_label(location);
					label_false = create_artificial_label(location);
					label_done = create_artificial_label(location);
					
					delta = create_tmp_var(long_integer_type_node, 
							SHADOW_ID_PREFIX("__exp_", "delta"));

					gimple_seq_add_stmt(&seq2,gimple_build_cond 
						(GT_EXPR, op1_exp, op2_exp,
							label_true, label_false));
					
					gimple_seq_add_stmt(&seq2, gimple_build_label(label_true));
					
					t = fold_build2(MINUS_EXPR,	long_unsigned_type_node, 
							op1_exp, op2_exp);
					gimplify_expr(&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
					g = gimple_build_assign(delta, t);
					gimple_set_location(g, location);
					gimple_seq_add_stmt(&seq2, g);

					g = gimple_build_goto(label_done);
					gimple_set_location(g, location);
					gimple_seq_add_stmt(&seq2, g);

					gimple_seq_add_stmt(&seq2, gimple_build_label(label_false));
					
					t = fold_build2(MINUS_EXPR,	long_unsigned_type_node, 
							op2_exp, op1_exp);
					gimplify_expr(&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
					g = gimple_build_assign(delta, t);
					gimple_set_location(g, location);
					gimple_seq_add_stmt(&seq2, g);
					
					gimple_seq_add_stmt(&seq2, gimple_build_label(label_done));
				}
				/* Main comparison */

				/* if (delta > EXP_CONSTANT_ONE) */
				{
					tree label_true1;
					tree label_true2;
					tree label_true3;
					tree label_done;
					
					label_true1 = create_artificial_label(location);
					label_true2 = create_artificial_label(location);
					label_true3 = create_artificial_label(location);
					label_done = create_artificial_label(location);

					gimple_seq_add_stmt (&seq2,	gimple_build_cond 
						(GT_EXPR, delta, build_int_cst 
						 (long_unsigned_type_node, EXP_CONSTANT_ONE),
						 label_true1, label_done));

					gimple_seq_add_stmt(&seq2, gimple_build_label(label_true1));
					
					gimple_seq_add_stmt(&seq2, gimple_build_cond 
						(NE_EXPR, op1_exp, 
						 build_int_cst(long_unsigned_type_node, 0),
						 label_true2, label_done));

					gimple_seq_add_stmt(&seq2, gimple_build_label(label_true2));

					gimple_seq_add_stmt(&seq2, gimple_build_cond 
						(NE_EXPR, op2_exp, 
						 build_int_cst(long_unsigned_type_node, 0),
						 label_true3, label_done));

					gimple_seq_add_stmt(&seq2, gimple_build_label(label_true3));

					t = build2(RSHIFT_EXPR, long_unsigned_type_node, delta,
							build_int_cst(integer_type_node, 52));

					g = gimple_build_call(lineage_acc_err_fndecl, 5, 
							op0, op1, op2, t, 
							lineage_build_string(
								detail_decl_info(unshare_expr(op0), location)));
					gimple_set_location(g, location);
					gimple_seq_add_stmt(&seq2, g);
					
					gimple_seq_add_stmt(&seq2, gimple_build_label(label_done));
				}
				
				/* 
				 * 2. Check for cancellation:
				 *    Compare the exp between op1 and op0, if not big enough,
				 *    compare the exp between op2 and op0. If true, call
				 *    large_cancel function, otherwise, exit.
				 */
				
				/* op0_ptr */
				op0_ptr = lineage_decls_mark(
							create_tmp_var(
								build_pointer_type(long_unsigned_type_node),
								SHADOW_ID_PREFIX("__op0_", "ptr")));

				t = build1(ADDR_EXPR, double_ptr_type_node, unshare_expr(op0));

				gimplify_expr(&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);

				t = build1(CONVERT_EXPR, 
						build_pointer_type(long_unsigned_type_node), t);

				g = gimple_build_assign(op0_ptr, t);
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq2, g);
				/* op0_exp */
				op0_exp = lineage_decls_mark(
							create_tmp_var(long_unsigned_type_node, 
							SHADOW_ID_PREFIX("__op0_", "exp")));

				t = build1(INDIRECT_REF, long_unsigned_type_node, op0_ptr);
				gimplify_expr(&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign(op0_exp, t);
				gimple_set_location (g, location);
				gimple_seq_add_stmt (&seq2, g);

				t = fold_build2(BIT_AND_EXPR, long_unsigned_type_node, op0_exp,
						build_int_cst(long_unsigned_type_node, EXP_MASK_LARGE));
				gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
				g = gimple_build_assign(op0_exp, t);
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq2, g);

				/* 
				 * delta1 = op1_exp - op0_exp; 
				 * delta2 = op2_exp - op0_exp; 
				 */
				{
					tree label_check1;
					tree label_check2;
					tree label_check3;
					tree label_cancel;
					tree label_done;
					tree t2;
					
					label_check1 = create_artificial_label(location);
					label_check2 = create_artificial_label(location);
					label_check3 = create_artificial_label(location);
					label_cancel = create_artificial_label(location);
					label_done = create_artificial_label(location);
					
					delta1 = create_tmp_var(long_unsigned_type_node, 
								SHADOW_ID_PREFIX("__exp_", "delta1"));
					
					delta2 = create_tmp_var(long_unsigned_type_node, 
								SHADOW_ID_PREFIX("__exp_", "delta2"));

					t = fold_build2(MINUS_EXPR,	long_unsigned_type_node, 
							op1_exp, op0_exp);
					gimplify_expr(&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
					g = gimple_build_assign(delta1, t);
					gimple_set_location(g, location);
					gimple_seq_add_stmt(&seq2, g);

					t = fold_build2(MINUS_EXPR,	long_unsigned_type_node, 
							op2_exp, op0_exp);
					gimplify_expr(&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
					g = gimple_build_assign(delta2, t);
					gimple_set_location(g, location);
					gimple_seq_add_stmt(&seq2, g);

					gimple_seq_add_stmt(&seq2,gimple_build_cond 
						(GT_EXPR, op1_exp, op0_exp,
						label_check1, label_check2));

					gimple_seq_add_stmt(&seq2, 
						gimple_build_label(label_check1));
					
					gimple_seq_add_stmt(&seq2,gimple_build_cond 
						(GT_EXPR, delta1, build_int_cst 
						(long_unsigned_type_node, EXP_THRESHOLD_LARGE),
						label_cancel, label_check2));
					
					gimple_seq_add_stmt(&seq2, 
						gimple_build_label(label_check2));
					
					gimple_seq_add_stmt(&seq2,gimple_build_cond 
						(GT_EXPR, op2_exp, op0_exp,
						label_check3, label_done));
					
					gimple_seq_add_stmt(&seq2, 
						gimple_build_label(label_check3));
					
					gimple_seq_add_stmt(&seq2,gimple_build_cond 
						(GT_EXPR, delta2, build_int_cst 
						(long_unsigned_type_node, EXP_THRESHOLD_LARGE),
						label_cancel, label_done));
					
					gimple_seq_add_stmt(&seq2, 
						gimple_build_label(label_cancel));
			
					t = build2(RSHIFT_EXPR, long_unsigned_type_node, delta1,
							build_int_cst(integer_type_node, 52));
					
					t2 = build2(RSHIFT_EXPR, long_unsigned_type_node, delta2,
							build_int_cst(integer_type_node, 52));

					g = gimple_build_call(lineage_large_cancel_fndecl, 6, 
							op0, op1, op2, t, t2,
							lineage_build_string(
								detail_decl_info(unshare_expr(op0), location)));
					gimple_set_location(g, location);
					gimple_seq_add_stmt(&seq2, g);
					
					gimple_seq_add_stmt(&seq2, 
						gimple_build_label(label_done));

				}
#endif
			}
			break;
		}
		case 32:
		{
			if ((TREE_CODE(TREE_TYPE(op0)) == REAL_TYPE) ||
				(TREE_CODE(TREE_TYPE(op1)) == REAL_TYPE) ||
				(TREE_CODE(TREE_TYPE(op2)) == REAL_TYPE))
			{
				tree t;
				gimple g;
				
#ifdef LINEAGE_RAND_ROUND	
				/* set rounding mode */
				g = gimple_build_call(lineage_random_rounding_mode_fndecl, 0);
				gimple_set_location(g, location);
				gimple_seq_add_stmt(&seq0, g);
#endif
			}
			break;
		}
		default:
		{
			/* We don't handle operations with size < 256 */
			printf("Do nothing: [%d]=[%d][%s][%d]\n", TYPE_SIZE_INT (op0),
				TYPE_SIZE_INT (op1), tree_code_name[op_code], 
				TYPE_SIZE_INT (op2));

			return;
		}
	}

	gimple_seq_add_stmt (&seq2, binop_fncall);

	/* Append to the mainline. */
	{
		gimple g;
		g = lineage_stmts_mark (gimple_build_bind (NULL, seq0, NULL));
		gimple_seq_add_stmt (seq0_p, g);
	}

	{
		gimple g;
		g = lineage_stmts_mark (gimple_build_bind (NULL, seq2, NULL));
		gimple_seq_add_stmt (seq2_p, g);
	}

	/* mark all */
	{
		struct walk_stmt_info wi;

		/* Mark all the stmts in the seq */
		memset (&wi, 0, sizeof (wi));
		wi.info = &location;
		walk_gimple_seq (*seq0_p, lineage_mark_seq, NULL, &wi);
		walk_gimple_seq (*seq2_p, lineage_mark_seq, NULL, &wi);
	}  
}

/*
 * Inline for division to check if op2's vector contains zero
 */
static void
lineage_inline_rdiv(gimple_stmt_iterator *gsi, gimple_seq *seq0_p, 
	gimple_seq *seq2_p, location_t location, 
	enum tree_code op_code ATTRIBUTE_UNUSED, 
	tree op0, tree op1, tree op2)
{
	gimple_seq seq0 = NULL;
	gimple_seq seq2 = NULL;
	gimple binop_fncall;
	tree lastDef;
	
	binop_fncall = gimple_build_nop ();
	
	if (TREE_CODE(op2) != VAR_DECL)
		return;

	if(DECL_ARTIFICIAL(op2) &&
	   (lastDef = lineage_get_last_def(gsi, op2)) &&
	   (TREE_CODE(lastDef) == CONSTRUCTOR ||
		TREE_CODE(lastDef) == VECTOR_CST)) 
	{
		return;
	}

	switch (TYPE_SIZE_INT (op0)) {
		case 256:
		{
			gimple g;
			/* 
			 * Checking for divide by zero and fix it in case that
			 * divisor is zero.
			 */
			tree vop2_ptr, op2_ptr1, op2_ptr2, op2_ptr3;
			tree op2_val1, op2_val2, op2_val3;
			tree label_val1_z, label_val1_nz, label_val2_z, label_val2_nz;
			tree t, zero, double_tmp;
			tree op2_tmp;

			vop2_ptr = lineage_decls_mark(create_tmp_var(
						build_pointer_type(v4df_type_node), 
						SHADOW_ID_PREFIX("__vop2", "_ptr")));

			op2_tmp = lineage_decls_mark(create_tmp_var(
						v4df_type_node, SHADOW_ID_PREFIX("__op2", "_tmp")));
			op2_ptr1 = lineage_decls_mark(create_tmp_var(
						double_ptr_type_node, SHADOW_ID_PREFIX("__op2", "_ptr1")));
			op2_ptr2 = lineage_decls_mark(create_tmp_var(
						double_ptr_type_node, SHADOW_ID_PREFIX("__op2", "_ptr2")));
			op2_ptr3 = lineage_decls_mark(create_tmp_var(
						double_ptr_type_node, SHADOW_ID_PREFIX("__op2", "_ptr3")));
			double_tmp = lineage_decls_mark(create_tmp_var(
						double_type_node, SHADOW_ID_PREFIX("__double", "_tmp")));

			g = gimple_build_assign(op2_tmp, unshare_expr(op2));
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);
			t = build1(ADDR_EXPR, 
					build_pointer_type(v4df_type_node), op2_tmp);
			gimplify_expr (&t, &seq0, &seq0, is_gimple_reg_rhs, fb_rvalue);

			g = gimple_build_assign(vop2_ptr, t);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			t = build1 (CONVERT_EXPR, double_ptr_type_node, vop2_ptr);
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign(op2_ptr1, t);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			zero = build_real_from_int_cst(
					double_type_node, build_int_cst(integer_type_node, 0));

			label_val1_z = create_artificial_label(location);
			label_val1_nz = create_artificial_label(location);
			label_val2_z = create_artificial_label(location);
			label_val2_nz = create_artificial_label(location);
			/* check element 1 */
			/* 1st element of op2 */
			op2_val1 = build1(INDIRECT_REF, double_type_node, op2_ptr1);
			gimplify_expr(&op2_val1, &seq0, &seq0, is_gimple_reg_rhs, 
					fb_rvalue);
			g = gimple_build_assign (double_tmp, op2_val1);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			gimple_seq_add_stmt(&seq0, gimple_build_cond 
					(EQ_EXPR, double_tmp, zero, label_val1_z, label_val1_nz));
			gimple_seq_add_stmt(&seq0, gimple_build_label(label_val1_z));
			
			t = build2 (POINTER_PLUS_EXPR, double_ptr_type_node, op2_ptr1, 
					build_int_cst (long_unsigned_type_node, 16));
			gimplify_expr (&t, &seq0, &seq0, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign (op2_ptr3, t);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			op2_val3 = build1 (INDIRECT_REF, double_type_node, op2_ptr3);
			gimplify_expr (&op2_val3, &seq0, &seq0, is_gimple_reg_rhs, 
					fb_rvalue);
			g = gimple_build_assign (double_tmp, op2_val3);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			g = gimple_build_assign (unshare_expr(op2_val1), double_tmp);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			g = gimple_build_assign(op2, op2_tmp);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			gimple_seq_add_stmt(&seq0, gimple_build_label(label_val1_nz));
			
			/* check element 2 */
			t = build2(POINTER_PLUS_EXPR, double_ptr_type_node, op2_ptr1, 
					build_int_cst (long_unsigned_type_node, 8));
			gimplify_expr(&t, &seq0, &seq0, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign(op2_ptr2, t);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			op2_val2 = build1(INDIRECT_REF, double_type_node, op2_ptr2);
			gimplify_expr(&op2_val2, &seq0, &seq0, is_gimple_reg_rhs,
					fb_rvalue);
			g = gimple_build_assign (double_tmp, op2_val2);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			gimple_seq_add_stmt(&seq0, gimple_build_cond 
					(EQ_EXPR, double_tmp, zero, label_val2_z, label_val2_nz));
			gimple_seq_add_stmt(&seq0, gimple_build_label(label_val2_z));

			/* fix 2nd element with 3rd element */
			t = build2 (POINTER_PLUS_EXPR, double_ptr_type_node, op2_ptr1, 
					build_int_cst (long_unsigned_type_node, 16));
			gimplify_expr (&t, &seq0, &seq0, is_gimple_reg_rhs, fb_rvalue);
			g = gimple_build_assign (op2_ptr3, t);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			op2_val3 = build1 (INDIRECT_REF, double_type_node, op2_ptr3);
			gimplify_expr (&op2_val3, &seq0, &seq0, is_gimple_reg_rhs, 
					fb_rvalue);
			g = gimple_build_assign (double_tmp, op2_val3);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			g = gimple_build_assign (unshare_expr(op2_val2), double_tmp);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			g = gimple_build_assign(op2, op2_tmp);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq0, g);

			gimple_seq_add_stmt(&seq0, gimple_build_label(label_val2_nz));
			break;
		}
		default:
		{
			/* We don't handle operations with size < 256 */
			printf("Do nothing: [%d]=[%d][%s][%d]\n", TYPE_SIZE_INT (op0),
				TYPE_SIZE_INT (op1), tree_code_name[op_code], 
				TYPE_SIZE_INT (op2));
			return;
		}
	}

	gimple_seq_add_stmt (&seq2, binop_fncall);

	/* Append to the mainline. */
	{
		gimple g;
		g = lineage_stmts_mark (gimple_build_bind (NULL, seq0, NULL));
		gimple_seq_add_stmt (seq0_p, g);
	}

	{
		gimple g;
		g = lineage_stmts_mark (gimple_build_bind (NULL, seq2, NULL));
		gimple_seq_add_stmt (seq2_p, g);
	}

	/* mark all */
	{
		struct walk_stmt_info wi;

		/* Mark all the stmts in the seq */
		memset (&wi, 0, sizeof (wi));
		wi.info = &location;
		walk_gimple_seq (*seq0_p, lineage_mark_seq, NULL, &wi);
		walk_gimple_seq (*seq2_p, lineage_mark_seq, NULL, &wi);
	}  
}
/*
 * Checking for nan for every lhs operand
 */
lineage_inline_check_nan(gimple_seq *seq0_p, gimple_seq *seq2_p, 
	location_t location, enum tree_code op_code ATTRIBUTE_UNUSED, 
	tree op0, tree op1, tree op2)
{
	gimple_seq seq0 = NULL;
	gimple_seq seq2 = NULL;

	gimple binop_fncall;
	binop_fncall = gimple_build_nop ();

	switch (TYPE_SIZE_INT (op0)) {
		case 256:
		{
			gimple g;
			tree vop0_ptr;
			tree op0_tmp, t;
		
			vop0_ptr = lineage_decls_mark(create_tmp_var(
				build_pointer_type(v4df_type_node), 
					SHADOW_ID_PREFIX("__vop0", "_ptr")));
			
			op0_tmp = lineage_decls_mark(create_tmp_var(
						v4df_type_node, SHADOW_ID_PREFIX("__op0", "_tmp")));
			
			g = gimple_build_assign(op0_tmp, unshare_expr(op0));
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq2, g);
			t = build1(ADDR_EXPR, 
					build_pointer_type(v4df_type_node), op0_tmp);
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);

			g = gimple_build_assign(vop0_ptr, t);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq2, g);

			g = gimple_build_call(inst_vec_check_nan_fndecl, 1, vop0_ptr);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);

			g = gimple_build_assign(unshare_expr(op0), op0_tmp);
			gimple_set_location(g, location);
			gimple_seq_add_stmt(&seq2, g);

			break;
		}
		default:
		{
			/* We don't handle operations with size < 256 */
			printf("Do nothing: [%d]=[%d]\n", TYPE_SIZE_INT (op0),
				TYPE_SIZE_INT (op1));
			break;
		}
	}
	
	gimple_seq_add_stmt (&seq2, binop_fncall);

	/* Append to the mainline. */
	{
		gimple g;
		g = lineage_stmts_mark (gimple_build_bind (NULL, seq0, NULL));
		gimple_seq_add_stmt (seq0_p, g);
	}

	{
		gimple g;
		g = lineage_stmts_mark (gimple_build_bind (NULL, seq2, NULL));
		gimple_seq_add_stmt (seq2_p, g);
	}

	/* mark all */
	{
		struct walk_stmt_info wi;

		/* Mark all the stmts in the seq */
		memset (&wi, 0, sizeof (wi));
		wi.info = &location;
		walk_gimple_seq (*seq0_p, lineage_mark_seq, NULL, &wi);
		walk_gimple_seq (*seq2_p, lineage_mark_seq, NULL, &wi);
	}  
}

static tree
lineage_get_array_addr(const tree decl, gimple_seq *seq_p, location_t location)
{
	tree array_shadow;
	struct walk_stmt_info wi;

	/* ta = &a[b] */
	tree tree_ab = build1 (ADDR_EXPR,
			build_pointer_type (TREE_TYPE (decl)), unshare_expr (decl));

	tree t1 = lineage_decls_mark (create_tmp_var (
				ptr_type_node, SHADOW_ID_PREFIX("__temp_", "array")));

	/* t1 = ta */
	array_shadow = build2 (MODIFY_EXPR, TREE_TYPE (t1), t1, tree_ab);

	gimplify_expr (&array_shadow, seq_p, NULL, is_gimple_lvalue, fb_lvalue);

	/* Mark all the stmts in the seq */
	memset (&wi, 0, sizeof (wi));
	wi.info = &location;
	walk_gimple_seq (*seq_p, lineage_mark_seq, NULL, &wi);

	return array_shadow;
}

static tree
lineage_get_component_addr (const tree decl, gimple_seq *seq_p, location_t location)
{
	struct walk_stmt_info wi;
	tree component_shadow;

	/* &(a->b) */
	tree tree_ab = build1 (ADDR_EXPR,
			build_pointer_type (TREE_TYPE (decl)), unshare_expr (decl));

	tree t1 = lineage_decls_mark (create_tmp_var (
				ptr_type_node, SHADOW_ID_PREFIX("__temp_", "component")));

	/* t1 = &(a->b) */
	component_shadow = build2 (MODIFY_EXPR, TREE_TYPE (t1), t1, tree_ab);

	gimplify_expr (&component_shadow, seq_p, NULL, is_gimple_lvalue, fb_lvalue);

	/* Mark all the stmts in the seq */
	memset (&wi, 0, sizeof (wi));
	wi.info = &location;
	walk_gimple_seq (*seq_p, lineage_mark_seq, NULL, &wi);

	return component_shadow;
}

static void
lineage_xfn_xform_fn_gimple_assign(gimple_stmt_iterator *gsi, gimple stmt)
{
	location_t location = gimple_location(stmt);
	
	switch (gimple_num_ops(stmt)) {
		case 3:
		{
			enum tree_code op_code;
			tree op0, op1, op2;

			op0 = gimple_assign_lhs(stmt);
			op1 = gimple_assign_rhs1(stmt);
			op2 = gimple_assign_rhs2(stmt);
			op_code = gimple_assign_rhs_code(stmt);

			fprintf(stderr, "\tCase 3: EXPR: %s [%ld]=[%ld][%ld]\n", 
				tree_code_name[op_code], TYPE_SIZE_INT(op0), 
				TYPE_SIZE_INT(op1), TYPE_SIZE_INT(op2));

			fprintf(stderr, 
				"\tOp0 type: %s\n\tOp1 type: %s\n\tOp2 type: %s\n", 
				tree_code_name[TREE_CODE(TREE_TYPE(op0))],
				tree_code_name[TREE_CODE(TREE_TYPE(op1))],
				tree_code_name[TREE_CODE(TREE_TYPE(op2))]);

#if 0
			if (op_code == POINTER_PLUS_EXPR) {
				fprintf (stderr, "ptr [op1]\n");
				debug_tree (op1);
				fprintf (stderr, "ptr [op2]\n");
				debug_tree (op2);
			}
#endif

			if (TREE_CODE (TREE_TYPE (op1)) == INTEGER_TYPE ||
				TREE_CODE (TREE_TYPE (op1)) == BOOLEAN_TYPE ||
				TREE_CODE (TREE_TYPE (op1)) == POINTER_TYPE ||
				TREE_CODE (TREE_TYPE (op1)) == ENUMERAL_TYPE ||
				op_code == POINTER_PLUS_EXPR)
				break;
			{
				gimple_seq seq_before = NULL;
				gimple_seq seq_after = NULL;
#if 0 
				fprintf (stderr, "[op1]\n");
				debug_tree (op1);
				fprintf (stderr, "[op2]\n");
				debug_tree (op2);

				/* instrument for checking equality of element 1 and element 2 */
				if (TYPE_SIZE_INT(op0) == 256) {
					gimple g;
					tree t;
					gimple_seq seq = NULL;

					t = build1(ADDR_EXPR, 
						build_pointer_type(v4df_type_node), op0);
					gimplify_expr (&t, &seq, &seq_before, is_gimple_reg_rhs, 
						fb_rvalue);

					g = gimple_build_call(lineage_check_equal_fndecl, 2, 
						t, lineage_build_string(detail_decl_info(op0, location)));
					gimple_set_location (g, location);
					gimple_seq_add_stmt (&seq, g);
		
					g = lineage_stmts_mark (gimple_build_bind (NULL, seq, NULL));
					gimple_seq_add_stmt (&seq_after, g);
				
					/* mark all */
					{
						struct walk_stmt_info wi;

						/* Mark all the stmts in the seq */
						memset (&wi, 0, sizeof (wi));
						wi.info = &location;
						walk_gimple_seq (seq_after, lineage_mark_seq, NULL, &wi);
					}  
				
				}
#endif

				if (op_code == PLUS_EXPR || op_code == MINUS_EXPR) {
					lineage_inline_plus_minus (&seq_before, &seq_after, 
						location, op_code, op0, op1, op2);
				} else if (flag_lineage_galgel &&
					(op_code == RDIV_EXPR || op_code == MULT_EXPR)) 
				{
					lineage_inline_check_nan (&seq_before, &seq_after, 
						location, op_code, op0, op1, op2);
				}

				gsi_insert_seq_before (gsi, seq_before, GSI_SAME_STMT);
				gsi_insert_seq_after (gsi, seq_after, GSI_SAME_STMT);

			}
			break;
		}

		case 2:
		{
			enum tree_code op_code;
			tree op0, op1, op2;
			gimple_seq seq_before = NULL;
			gimple_seq seq_after = NULL;

			op0 = gimple_assign_lhs(stmt);
			op1 = gimple_assign_rhs1(stmt);
			op_code = gimple_assign_rhs_code(stmt);
			
			fprintf(stderr, "\tCase 2: EXPR: %s [%ld]=[%ld]\n", 
				tree_code_name[op_code], TYPE_SIZE_INT(op0), 
				TYPE_SIZE_INT(op1));
			fprintf(stderr, 
				"\tOp0 type: %s\n\tOp1 type: %s\n", 
				tree_code_name[TREE_CODE(TREE_TYPE(op0))],
				tree_code_name[TREE_CODE(TREE_TYPE(op1))]);
			break;
		}
		case 1:
			fprintf (stderr, "case 1\n");
			gcc_unreachable ();
			break;

		default:
			fprintf (stderr, "default\n");
			gcc_unreachable ();
			break;
	}

	fprintf (stderr, "\n");

}

#ifndef NORMAL_VEC
/* 
 * Used for lhs mapping because we want to backup original value of
 * lhs for duplicated assign statements
 */
void *lhs_table[1024][2];
int lhs_table_idx;
/**/
void *label_table[1024][2];
int label_table_idx;

static tree lineage_search_match_label(tree label, location_t loc)
{
	int i;
	unsigned int search_uid = DECL_UID(label);

	for (i=0; i<label_table_idx; i++) {
		tree src_uid = DECL_UID((tree)label_table[i][0]);

		if (src_uid == search_uid)
			return label_table[i][1];
	}

	label_table[label_table_idx][0] = label;
	label_table[label_table_idx][1] = create_artificial_label(loc);

	return label_table[label_table_idx++][1];
}
/*
 * This is used to handle problematic statements inside continuous core.
 * Because we want to duplicate the statements inside continuous core 
 * for testing, we need to make sure that gcc can continue after we
 * duplicate statements inside the core.
 */
static gimple lineage_handle_stmt(gimple stmt, 
	struct gimple_seq_node_d *pSeqNode, tree src_f_label)
{
	location_t loc = gimple_location(stmt);
	gimple dup_stmt = NULL;

	switch (gimple_code(stmt)) {
		case GIMPLE_COND:
		{
			dup_stmt = gimple_copy(stmt);
			tree t_label = gimple_cond_true_label(stmt);
			tree f_label = gimple_cond_false_label(stmt);
			tree new_t_label = lineage_search_match_label(t_label, loc);
			tree new_f_label = lineage_search_match_label(f_label, loc);
		
			gimple_cond_set_true_label (dup_stmt, unshare_expr(new_t_label));
			gimple_cond_set_false_label (dup_stmt, unshare_expr(new_f_label));

			break;
		}
		case GIMPLE_LABEL:
		{
			dup_stmt = gimple_copy(stmt);
			tree label = gimple_label_label(stmt);
			tree new_label = lineage_search_match_label(label, loc);
			gimple_label_set_label(dup_stmt, unshare_expr(new_label));

			break;
		}
		case GIMPLE_GOTO:
		{
			gimple g;
			tree goto_label = gimple_goto_dest (stmt);

			for (g=pSeqNode->stmt;	
				 gimple_code(g) != GIMPLE_LABEL ||
				 DECL_UID(gimple_label_label(g)) != DECL_UID(src_f_label);
				 pSeqNode=pSeqNode->next, g=pSeqNode->stmt) 
			{
				if (gimple_code(g) == GIMPLE_LABEL &&
					DECL_UID(gimple_label_label(g)) == DECL_UID(goto_label)) 
				{
					
					tree new_goto_label = 
						lineage_search_match_label(goto_label, loc);
					
					dup_stmt = gimple_copy(stmt);
					
					gimple_goto_set_dest(dup_stmt, new_goto_label);
					
					printf("%u %u\n", 
						DECL_UID(src_f_label), DECL_UID(goto_label));
					print_gimple_stmt(stderr, dup_stmt, 0, TDF_RAW);
					
					return dup_stmt;
				}
			}

			dup_stmt = gimple_build_nop();

			break;
		}
		case GIMPLE_BIND:
		case GIMPLE_CALL:
		{
			dup_stmt = gimple_build_nop();
			break;
		}
		default:
			return NULL;
	}

	print_gimple_stmt(stderr, dup_stmt, 0, TDF_RAW);

	return dup_stmt;
}

static int lineage_bypass_func()
{
	const char *decl_file = 
		DECL_SOURCE_FILE (current_function_decl);
	const char *decl_name = 
		lang_hooks.decl_printable_name(current_function_decl, 2);

	if (flag_lineage_kmeans) {
		if (strncmp(decl_file, "cluster.c", 9) == 0 &&
			strncmp(decl_name, "kmeans", 6) == 0)
			return 0;
		else return 1;
	} 
	if (flag_lineage_deisotope || flag_lineage_galgel) {
		return 1;
	} 

	return 0;
}
/*
 * Handle continuous core testing
 *
 * seq2: Sequence of statements to be instrumented after current stmt
 * stable_label: label for branch if this is a true continuous core
 */
static void 
lineage_handle_concore(gimple_stmt_iterator *gsi, gimple_seq *seq2, 
	tree stable_label)
{
	tree t_label, f_label;
	unsigned int label_diff;
	gimple_seq seq = NULL;
	struct gimple_seq_node_d *pSeqNode;
	gimple stmt;
	location_t location;
	int i;
	gimple g;

	pSeqNode = gsi->ptr;
	stmt = pSeqNode->stmt;
	location = gimple_location (stmt);

	t_label = gimple_cond_true_label(stmt);
	f_label = gimple_cond_false_label(stmt);

	label_diff = DECL_UID(f_label) - DECL_UID(t_label);
	
	/* No handling of loop currently */
	if (label_diff > 1 || lineage_bypass_func())
		return;

	print_gimple_stmt(stdout, gsi->ptr->stmt, 0, TDF_RAW);
	/* Get statements inside true branch */
	gcc_assert(gimple_code(pSeqNode->next->stmt) == GIMPLE_LABEL &&
		gimple_label_label(pSeqNode->next->stmt) == t_label);

	/* Bypass true label */
	pSeqNode = pSeqNode->next->next;

	lhs_table_idx = 0;
	label_table_idx = 0;
	/* Check for assign statements and backup the lhs */

	printf("1\n");
	for (stmt = pSeqNode->stmt;
		 gimple_code(stmt) != GIMPLE_LABEL ||
		 DECL_UID(gimple_label_label(stmt)) != DECL_UID(f_label);
		 pSeqNode = pSeqNode->next, stmt = pSeqNode->stmt) 
	{
		tree lhs;
		tree type;
		tree tmp_lhs;
		tree decl_lhs;

		if (is_gimple_assign(stmt)) {
			decl_lhs = lhs = gimple_assign_lhs(stmt);
			type = TREE_TYPE(lhs);

			/* Get the real declared variable */
			if (TREE_CODE(lhs) == MEM_REF || TREE_CODE(lhs) == ARRAY_REF ||
					TREE_CODE(lhs) == COMPONENT_REF)
				decl_lhs = TREE_OPERAND(lhs, 0);

			if (DECL_ARTIFICIAL(decl_lhs) && TREE_CODE(lhs) != MEM_REF && 
				TREE_CODE(lhs) != ARRAY_REF && TREE_CODE(lhs) != COMPONENT_REF)
				goto dupStmt;
			
			tmp_lhs = create_tmp_var (type, 
					SHADOW_ID_PREFIX("__tmp", "_lhs"));

			/* Save lhs mapping for later restore */
			lhs_table[lhs_table_idx][0] = lhs;
			lhs_table[lhs_table_idx++][1] = tmp_lhs;

			g = gimple_build_assign (tmp_lhs, unshare_expr(lhs));
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq, g);
		}
dupStmt:
		/* Check for branch, bind, ... statements inside continuous core */
		g = lineage_handle_stmt(stmt, pSeqNode, f_label);

		/* Duplicate statements inside continuous core */
		if (!g)
			g = gimple_copy(stmt);

		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq, g);
	}

	/* Check for real unstable */
	tree unstable_label;
	unstable_label = create_artificial_label (location);

	for (i=0; i<lhs_table_idx; i++) {
		tree lhs = lhs_table[i][0];
		tree tmp_lhs = lhs_table[i][1];
		tree lhs_ptr;
		tree tmp_lhs_ptr;
		tree type = TREE_TYPE(lhs);
		tree t, rtn;
		tree next_label;

		next_label = create_artificial_label(location);

		rtn = create_tmp_var (integer_type_node, 
				SHADOW_ID_PREFIX("__rtn", ""));
	
		lhs_ptr = build1 (ADDR_EXPR, build_pointer_type(type), 
				unshare_expr(lhs));

		gimplify_expr (&lhs_ptr, &seq, &seq, 
				is_gimple_reg_rhs, fb_rvalue);

		tmp_lhs_ptr = build1 (ADDR_EXPR, build_pointer_type(type), 
				unshare_expr(tmp_lhs));
		gimplify_expr (&tmp_lhs_ptr, &seq, &seq, 
				is_gimple_reg_rhs, fb_rvalue);

		g = gimple_build_call(lineage_check_concore_fndecl, 5, 
				lhs_ptr, tmp_lhs_ptr, 
				build_int_cst(integer_type_node, TREE_CODE(type)),
				(i == lhs_table_idx-1) ?
				build_int_cst(integer_type_node, 1) :
				build_int_cst(integer_type_node, 0),
				lineage_build_string(detail_decl_info(lhs, location)));
		
		gimple_call_set_lhs(g, rtn);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq, g);

		gimple_seq_add_stmt (&seq,
			gimple_build_cond (EQ_EXPR, unshare_expr(rtn), 
				build_int_cst(integer_type_node, 1),
				unstable_label, next_label));

		gimple_seq_add_stmt (&seq, gimple_build_label (next_label));

	}
	printf("4\n");
	/* write back pre-stored lhs for stable */
	for (i=lhs_table_idx-1; i>=0; i--) {

		g = gimple_build_assign (unshare_expr(lhs_table[i][0]), 
			unshare_expr(lhs_table[i][1]));
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq, g);
	}
	
	g = gimple_build_goto(stable_label);
	gimple_set_location (g, location);
	gimple_seq_add_stmt (&seq, g);
	
	gimple_seq_add_stmt (&seq, gimple_build_label (unstable_label));

	printf("5\n");
	/* write back pre-stored lhs for unstable */
	for (i=lhs_table_idx-1; i>=0; i--) {
		g = gimple_build_assign (unshare_expr(lhs_table[i][0]), 
			unshare_expr(lhs_table[i][1]));
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq, g);
	}
	
	printf("6\n");
	print_gimple_stmt(stdout, gsi->ptr->stmt, 0, 0);
	
	{
		g = lineage_stmts_mark (gimple_build_bind (NULL, seq, NULL));
		gimple_seq_add_stmt (seq2, g);
	}
}

/*
 * Instrument at predicate to test its stability.
 */
void
lineage_patch_predicate256(gimple_stmt_iterator *gsi, gimple stmt)
{
	location_t location = gimple_location (stmt);

	gimple_seq seq2 = NULL;

	enum tree_code op_code;
	tree op;
	tree vlhs, vrhs;
	tree vlhs_ptr, vrhs_ptr;
	tree lhs_ptr, rhs_ptr;
	tree rtn_v1, rtn_v2, rtn_v3;
	/* Left double of lhs vector */
	tree lhs_v1, lhs_v2, lhs_v3;
	/* Left double of rhs vector */
	tree rhs_v1, rhs_v2, rhs_v3;
	gimple prevStmt;
	tree decl_lhs = NULL, decl_rhs = NULL;

	gcc_assert (gimple_code (stmt) == GIMPLE_COND);

	op_code = gimple_cond_code (stmt);
	vlhs = gimple_cond_lhs (stmt);
	vrhs = gimple_cond_rhs (stmt);

	/* 
	 * Get the real declared variable
	 * Note: Don't take constant's tree node
	 */
	
	if (TREE_CODE(vlhs) == VAR_DECL)
		decl_lhs = DECL_ARTIFICIAL(vlhs) ?
			lineage_get_decl_var_rec(gsi->ptr->prev, vlhs) : 
			unshare_expr(vlhs);
	
	if (TREE_CODE(vrhs) == VAR_DECL)
		decl_rhs = DECL_ARTIFICIAL(vrhs) ?
			lineage_get_decl_var_rec(gsi->ptr->prev, vrhs) : 
			unshare_expr(vrhs);

	/* Get the values of lhs vector */
	{
		tree t;
		gimple g;

		/* Variables declaration */
		lhs_v1 = lineage_decls_mark(create_tmp_var(
				double_type_node, SHADOW_ID_PREFIX("__lhs", "_v1")));
		
		DECL_ALIGN (lhs_v1) = (32) * BITS_PER_UNIT;
		DECL_USER_ALIGN (lhs_v1) = 1;

		lhs_v2 = lineage_decls_mark(create_tmp_var(
				double_type_node, SHADOW_ID_PREFIX("__lhs", "_v2")));
		
		DECL_ALIGN (lhs_v2) = (32) * BITS_PER_UNIT;
		DECL_USER_ALIGN (lhs_v2) = 1;
		
		lhs_v3 = lineage_decls_mark(create_tmp_var(
				double_type_node, SHADOW_ID_PREFIX("__lhs", "_v3")));
		
		DECL_ALIGN (lhs_v3) = (32) * BITS_PER_UNIT;
		DECL_USER_ALIGN (lhs_v3) = 1;

		/* 
		 * Create a double type pointer and point to the lhs vector
		 */
		vlhs_ptr = build1 (ADDR_EXPR, build_pointer_type(
				v4df_type_node), vlhs);
		gimplify_expr (&vlhs_ptr, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);

		lhs_ptr = lineage_decls_mark (create_tmp_var (
				double_ptr_type_node, SHADOW_ID_PREFIX("__lhs", "_ptr")));
		g = gimple_build_assign (lhs_ptr, vlhs_ptr);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);

		/* Get lhs_v1 */
		t = build1 (INDIRECT_REF, double_type_node, lhs_ptr);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (lhs_v1, t);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);

		/* Add 8 bytes to lhs_ptr */
		t = build2 (POINTER_PLUS_EXPR, double_ptr_type_node, lhs_ptr, 
				build_int_cst (long_unsigned_type_node, 8));
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);

		/* Get lhs_v2 */
		t = build1 (INDIRECT_REF, double_type_node, t);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (lhs_v2, t);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);
		
		/* Add 16 bytes to lhs_ptr */
		t = build2 (POINTER_PLUS_EXPR, double_ptr_type_node, lhs_ptr, 
				build_int_cst (long_unsigned_type_node, 16));
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);

		/* Get lhs_v3 */
		t = build1 (INDIRECT_REF, double_type_node, t);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (lhs_v3, t);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);
	}

	/* Get the values of rhs vector */
	{
		tree t;
		gimple g;

		rhs_v1 = lineage_decls_mark (create_tmp_var (
				double_type_node, SHADOW_ID_PREFIX("__rhs", "_v1")));
		
		DECL_ALIGN (rhs_v1) = (32) * BITS_PER_UNIT;
		DECL_USER_ALIGN (rhs_v1) = 1;

		rhs_v2 = lineage_decls_mark (create_tmp_var (
				double_type_node, SHADOW_ID_PREFIX("__rhs", "_v2")));
		
		DECL_ALIGN (rhs_v2) = (32) * BITS_PER_UNIT;
		DECL_USER_ALIGN (rhs_v2) = 1;
		
		rhs_v3 = lineage_decls_mark (create_tmp_var (
				double_type_node, SHADOW_ID_PREFIX("__rhs", "_v3")));
		
		DECL_ALIGN (rhs_v3) = (32) * BITS_PER_UNIT;
		DECL_USER_ALIGN (rhs_v3) = 1;

		/* 
		 * Create a double type pointer and point to the rhs vector
		 */
		vrhs_ptr = build1 (ADDR_EXPR, build_pointer_type (v4df_type_node), 
				vrhs);
		gimplify_expr (&vrhs_ptr, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);

		rhs_ptr = lineage_decls_mark (create_tmp_var (
				double_ptr_type_node, SHADOW_ID_PREFIX("__rhs_", "ptr")));
		g = gimple_build_assign (rhs_ptr, vrhs_ptr);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);

		/* Get rhs_v1 */
		t = build1 (INDIRECT_REF, double_type_node, rhs_ptr);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (rhs_v1, t);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);

		t = build2 (POINTER_PLUS_EXPR, double_ptr_type_node, rhs_ptr, 
				build_int_cst (long_unsigned_type_node, 8));
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		
		/* Get rhs_v2 */
		t = build1 (INDIRECT_REF, double_type_node, t);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (rhs_v2, t);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);
#if 0		
		t = build2 (POINTER_PLUS_EXPR, double_ptr_type_node, rhs_ptr, 
				build_int_cst (long_unsigned_type_node, 16));
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		
		/* Get rhs_v3 */
		t = build1 (INDIRECT_REF, double_type_node, t);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (rhs_v3, t);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);
#endif
	}

	/* 
	 * Check the stability of a predicate 
	 */
	{
		tree t;
		gimple g;

		rtn_v1 = create_tmp_var (integer_type_node, 
				SHADOW_ID_PREFIX("__rtn", "_v1"));
		
		rtn_v2 = create_tmp_var (integer_type_node, 
				SHADOW_ID_PREFIX("__rtn", "_v2"));
		
		rtn_v3 = create_tmp_var (integer_type_node, 
				SHADOW_ID_PREFIX("__rtn", "_v3"));
		
		t = fold_build2 (op_code, integer_type_node, lhs_v1, rhs_v1);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (rtn_v1, t);
 		gimple_set_location (g, location);
 		gimple_seq_add_stmt (&seq2, g);

		t = fold_build2 (op_code, integer_type_node, lhs_v2, rhs_v2);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (rtn_v2, t);
 		gimple_set_location (g, location);
 		gimple_seq_add_stmt (&seq2, g);
#if 0	
		t = fold_build2 (op_code, integer_type_node, lhs_v3, rhs_v3);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (rtn_v3, t);
 		gimple_set_location (g, location);
 		gimple_seq_add_stmt (&seq2, g);
#endif
	}
	/* Compare the results */
	{
		tree t, cmp;
		gimple g;
		tree label_p1, label_check_and_set_done;

		cmp = create_tmp_var (boolean_type_node, 
				SHADOW_ID_PREFIX("__cmp", ""));

		t = fold_build2 (EQ_EXPR, boolean_type_node, rtn_v1, rtn_v2);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (cmp, t);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);

		label_p1 = create_artificial_label (location);
		label_check_and_set_done = create_artificial_label (location);

		/* 
		 * If results are different, then we should do split by calling
		 * lineage_spawn, else continue execution.
		 */
		gimple_seq_add_stmt (&seq2,
				gimple_build_cond (EQ_EXPR, cmp, boolean_false_node,
				label_p1, label_check_and_set_done));

		gimple_seq_add_stmt (&seq2, gimple_build_label (label_p1));

		/* Continuous core test */

		lineage_handle_concore(gsi, &seq2, label_check_and_set_done);

		g = gimple_build_call(lineage_spawn_fndecl, 6, 
				rtn_v1, rtn_v2, rtn_v1, vlhs_ptr, vrhs_ptr, 
				lineage_build_string(detail_decl_info(vlhs, location)));
		gimple_call_set_lhs(g, rtn_v1);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);
	
		/* Overwrite the value of original declared variable of lhs */
		if (decl_lhs && TREE_CODE(decl_lhs) == VAR_DECL) {
			t = build1 (INDIRECT_REF, v4df_type_node, vlhs_ptr);
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);

			g = gimple_build_assign(decl_lhs, t);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);
		}

		/* Overwrite the value of original declared variable of rhs */
		if (decl_rhs && TREE_CODE(decl_rhs) == VAR_DECL) {
			t = build1 (INDIRECT_REF, v4df_type_node, vrhs_ptr);
			gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
			
			g = gimple_build_assign (decl_rhs, t);
			gimple_set_location (g, location);
			gimple_seq_add_stmt (&seq2, g);
		}
		gimple_seq_add_stmt (&seq2, gimple_build_label (
			label_check_and_set_done));

	}
	
	/* mark all */
	{
		struct walk_stmt_info wi;

		/* Mark all the stmts in the seq */
		memset (&wi, 0, sizeof (wi));
		wi.info = &location;
		walk_gimple_seq (seq2, lineage_mark_seq, NULL, &wi);
	}

	/* Append to the mainline. */
	{
		gimple g;
		gimple_seq seq = NULL;

		g = lineage_stmts_mark (gimple_build_bind (NULL, seq2, NULL));
		gimple_seq_add_stmt (&seq, g);
		gsi_insert_seq_before (gsi, seq, GSI_SAME_STMT);
	}

	/* 
	 * Originally, the program will execute according to the evaluation
	 * result of current condition. However, if this predicate is 
	 * unstable, rtn_v1 will be different for parent process and child 
	 * process, then parent and child will continue their executions on 
	 * different path.
	 */
	gimple_cond_set_condition(stmt, EQ_EXPR, rtn_v1, boolean_true_node);
	return;
}
#else
lineage_patch_predicate256(gimple_stmt_iterator *gsi, gimple stmt)
{
	location_t location = gimple_location (stmt);

	gimple_seq seq2 = NULL;

	enum tree_code op_code;
	tree op;
	tree vlhs, vrhs;
	tree vlhs_ptr, vrhs_ptr;
	tree lhs_ptr, rhs_ptr;
	tree rtn_v1, rtn_v2, rtn_v3;
	/* Left double of lhs vector */
	tree lhs_v1, lhs_v2, lhs_v3;
	/* Left double of rhs vector */
	tree rhs_v1, rhs_v2, rhs_v3;
	gimple prevStmt;
	tree decl_lhs = NULL, decl_rhs = NULL;

	gcc_assert (gimple_code (stmt) == GIMPLE_COND);

	op_code = gimple_cond_code (stmt);
	vlhs = gimple_cond_lhs (stmt);
	vrhs = gimple_cond_rhs (stmt);


	/* Get the values of lhs vector */
	{
		tree t;
		gimple g;

		/* Variables declaration */
		lhs_v1 = lineage_decls_mark(create_tmp_var(
				double_type_node, SHADOW_ID_PREFIX("__lhs", "_v1")));
		
		DECL_ALIGN (lhs_v1) = (32) * BITS_PER_UNIT;
		DECL_USER_ALIGN (lhs_v1) = 1;

		/* 
		 * Create a double type pointer and point to the lhs vector
		 */
		vlhs_ptr = build1 (ADDR_EXPR, build_pointer_type(
				v4df_type_node), vlhs);
		gimplify_expr (&vlhs_ptr, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);

		lhs_ptr = lineage_decls_mark (create_tmp_var (
				double_ptr_type_node, SHADOW_ID_PREFIX("__lhs", "_ptr")));
		g = gimple_build_assign (lhs_ptr, vlhs_ptr);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);

		/* Get lhs_v1 */
		t = build1 (INDIRECT_REF, double_type_node, lhs_ptr);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (lhs_v1, t);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);
	}

	/* Get the values of rhs vector */
	{
		tree t;
		gimple g;

		rhs_v1 = lineage_decls_mark (create_tmp_var (
				double_type_node, SHADOW_ID_PREFIX("__rhs", "_v1")));
		
		DECL_ALIGN (rhs_v1) = (32) * BITS_PER_UNIT;
		DECL_USER_ALIGN (rhs_v1) = 1;

		/* 
		 * Create a double type pointer and point to the rhs vector
		 */
		vrhs_ptr = build1 (ADDR_EXPR, build_pointer_type (v4df_type_node), 
				vrhs);
		gimplify_expr (&vrhs_ptr, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);

		rhs_ptr = lineage_decls_mark (create_tmp_var (
				double_ptr_type_node, SHADOW_ID_PREFIX("__rhs_", "ptr")));
		g = gimple_build_assign (rhs_ptr, vrhs_ptr);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);

		/* Get rhs_v1 */
		t = build1 (INDIRECT_REF, double_type_node, rhs_ptr);
		gimplify_expr (&t, &seq2, &seq2, is_gimple_reg_rhs, fb_rvalue);
		g = gimple_build_assign (rhs_v1, t);
		gimple_set_location (g, location);
		gimple_seq_add_stmt (&seq2, g);
	}
	
	/* mark all */
	{
		struct walk_stmt_info wi;

		/* Mark all the stmts in the seq */
		memset (&wi, 0, sizeof (wi));
		wi.info = &location;
		walk_gimple_seq (seq2, lineage_mark_seq, NULL, &wi);
	}

	/* Append to the mainline. */
	{
		gimple g;
		gimple_seq seq = NULL;

		g = lineage_stmts_mark (gimple_build_bind (NULL, seq2, NULL));
		gimple_seq_add_stmt (&seq, g);
		gsi_insert_seq_before (gsi, seq, GSI_SAME_STMT);
	}

	/* 
	 * Originally, the program will execute according to the evaluation
	 * result of current condition. However, if this predicate is 
	 * unstable, rtn_v1 will be different for parent process and child 
	 * process, then parent and child will continue their executions on 
	 * different path.
	 */
	gimple_cond_set_condition(stmt, op_code, lhs_v1, rhs_v1);
	return;
}
#endif

static void
lineage_xfn_xform_fn_gimple_call(gimple_stmt_iterator *gsi, gimple stmt)
{
	tree fndecl = gimple_call_fndecl (stmt);
	const char *callee_name;

	/* already marked */
	if (lineage_stmts_marked_p(stmt))
		return;      
	/* 
	 * Function pointer, the callee is VAR_DECL instead of 
	 * ADDR_EXPR->FUNCTION_DECL 
	 */
	if (fndecl == NULL_TREE) {
		tree addr = gimple_call_fn(stmt);
		callee_name = ID_PTR_NAME(addr);
		fprintf(stderr, "null fndecl!\n");
	} else {
		callee_name = ID_PTR_NAME(fndecl);
	}

	return;
}

/* 
 * Process every variable and every statement 
 * mentioned in BIND_EXPRs. 
 */
static tree
lineage_xfn_xform_fn (gimple_stmt_iterator *gsi,
	bool *handled_operands_p ATTRIBUTE_UNUSED,
	struct walk_stmt_info *wi ATTRIBUTE_UNUSED)
{
	struct lineage_xform_decls_data *d = 
		(struct lineage_xform_decls_data *) wi->info;

	gimple stmt = gsi_stmt (*gsi);
	location_t location = gimple_location (stmt);

	if (lineage_stmts_marked_p (stmt))
		goto leave;

	fprintf (stderr, "\n-- %s [%d]\n", 
			gimple_code_name[(int) gimple_code (stmt)], 
			lineage_stmts_marked_p (stmt));
	print_gimple_stmt(stderr, stmt, 0, 0);

	if (gimple_code (stmt) != GIMPLE_BIND && 
		gimple_code (stmt) != GIMPLE_TRY) 
	{
	//	debug_gimple_stmt (stmt);
	}

	switch (gimple_code (stmt)) {
		case GIMPLE_BIND:
		{
			/* Process function parameters now (but only once).  */
			if (d->param_decls)
				d->param_decls = NULL_TREE;

			if (!top_bind)
				top_bind = stmt;

			break;
		}

		case GIMPLE_ASSIGN:
		{
#ifndef NORMAL_VEC
			lineage_xfn_xform_fn_gimple_assign (gsi, stmt);
#endif
			break;
		}

		case GIMPLE_CALL:
		{
			lineage_xfn_xform_fn_gimple_call (gsi, stmt);
			break;
		}

		case GIMPLE_COND:
		{
			/* 
			 * NOTE: generate calls before predicates 
			 * The rest are done in lineage-fp.c (VEC)
			 */
			break;
		}

		case GIMPLE_LABEL:
		{
			break;
		}

		default:
			break;
	}

leave:
	return NULL_TREE;
}

/* 
 * Perform the object lifetime tracking mudflap transform on the given function
 * tree.  The tree is mutated in place, with possibly copied subtree nodes.
 * For every auto variable declared, if its address is ever taken
 * within the function, then supply its lifetime to the mudflap
 * runtime with the __mf_register and __mf_unregister calls.
 */
static void
lineage_xform_fn(gimple_seq fnbody, tree fnparams)
{
	struct lineage_xform_decls_data d;
	struct walk_stmt_info wi;
	struct pointer_set_t *pset;

	allocate_seq = NULL;
	top_bind = NULL;

	pset = pointer_set_create ();
	d.param_decls = fnparams;
	memset (&wi, 0, sizeof (wi));
	wi.info = (void *) &d;
	wi.pset = pset;
	walk_gimple_seq (fnbody, lineage_xfn_xform_fn, NULL, &wi);
	pointer_set_destroy (pset);

	gcc_assert (top_bind != NULL);
	/* Insert allocate_seq */
	{
		gimple_seq seq = gimple_bind_body (top_bind);
		gimple_stmt_iterator initially_stmts = gsi_start (seq);
		gsi_insert_seq_before (&initially_stmts, allocate_seq, GSI_SAME_STMT);
		gimple_bind_set_body (top_bind, seq);    
	}
}

/* Emit any file-wide instrumentation.  */
void
lineage_finish_file (void)
{
	tree ctor_statements = NULL_TREE;
	tree dtor_statements = NULL_TREE;

	/* No need to continue when there were errors.  */
	if (errorcount != 0 || sorrycount != 0)
		return;

	/* Generate calls to init and fini only if have seen main */
	if (!see_main_p)
		return;

	/* TODO: mark these stmts */

	fprintf (stderr, "*****FINISH_FILE*****\n");

	/* Insert a call to __lineage_init.  */
	{
		tree call2_stmt = 
			build_call_expr(lineage_init_fndecl, 1, 
				build_int_cst(integer_type_node, EXP_THRESHOLD));
		append_to_statement_list (call2_stmt, &ctor_statements);
	}

	cgraph_build_static_cdtor ('I', ctor_statements, 
			MAX_RESERVED_INIT_PRIORITY-1);

	/* Insert a call to __lineage_fini.  */
	{
		tree call2_stmt = build_call_expr (lineage_fini_fndecl, 0);
		append_to_statement_list (call2_stmt, &dtor_statements);
	}

	cgraph_build_static_cdtor ('D', dtor_statements, 
			MAX_RESERVED_INIT_PRIORITY-1);
}


static unsigned int do_lineage (void)
{
#if 0
  struct gimplify_ctx gctx;
	const char *decl_name = 
		lang_hooks.decl_printable_name(current_function_decl, 2);

	fprintf (stderr, ";; ========================\n");
	fprintf (stderr, ";; [do_lineage] %s\n", decl_name);
	fprintf (stderr, ";; ========================\n");

	if (MAIN_NAME_P (DECL_NAME (current_function_decl))) {
		/* Only one main node */
		gcc_assert (!see_main_p);
		see_main_p = 1;
		fprintf (stderr, "MAIN\n");
	}

	/* 
	 * Skip built-in _mm intrinsic functions 
	 * These functions are vectorization operations.
	 */
	if (!strncmp (decl_name, "_mm", 3)) {
		fprintf (stderr, "Skipping [%s].\n", decl_name);
		return 0;
	}

	if (strcmp(decl_name, "resid") == 0) {
		fprintf (stderr, "Skipping [%s].\n", decl_name);
		return 0;
	}
	push_gimplify_context (&gctx);

#ifndef TESTING_INLINE

	lineage_xform_fn (gimple_body (current_function_decl),
		DECL_ARGUMENTS (current_function_decl));
#endif

	pop_gimplify_context (
			gimple_seq_first_stmt (gimple_body (current_function_decl)));
#endif
	return 0;
}

/* The pass gate. */
static bool
gate_lineage (void)
{
#if 0
	return 0;
#else
	return (flag_lineage != 0);
#endif
}

struct gimple_opt_pass pass_lineage =
{
	{
		GIMPLE_PASS,
		"lineage",                    /* name */
		gate_lineage,                 /* gate */
		do_lineage,                   /* execute */
		NULL,                         /* sub */
		NULL,                         /* next */
		0,                            /* static_pass_number */
		TV_NONE,                      /* tv_id */
		PROP_cfg,                     /* properties_required */
		0,                            /* properties_provided */
		0,                            /* properties_destroyed */
		0,                            /* todo_flags_start */
		TODO_dump_func                /* todo_flags_finish */
	}
};

struct gimple_opt_pass pass_pre_lineage =
{
	{
		GIMPLE_PASS,
		"prelineage",                 /* name */
		gate_lineage,                 /* gate */
		NULL,                         /* execute */
		NULL,                         /* sub */
		NULL,                         /* next */
		0,                            /* static_pass_number */
		TV_NONE,                      /* tv_id */
		PROP_gimple_any,              /* properties_required */
		0,                            /* properties_provided */
		0,                            /* properties_destroyed */
		0,                            /* todo_flags_start */
		TODO_dump_func                /* todo_flags_finish */
	}
};

