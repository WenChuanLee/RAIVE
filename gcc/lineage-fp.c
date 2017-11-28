/* lineage-fp.c
 * 
 * The name stands for lineage-fix-predicate, or lineage-floating-point. It 
 * handles issues caused by 256-bit vector comparisons which will otherwise
 * panic the compilation.
 */

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


#define LINEAGE_ID_LEN                            128

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


/* This struct is passed between lineage_xform_decls to store state needed
   during the traversal searching for objects that have their
   addresses taken.  */
struct lineage_xform_decls_data
{
	tree param_decls;
};


/* void lineage_icmp256_fndecl (int, v4df, v4df) */
static GTY (()) tree lineage_icmp256_fndecl;

/* void * memalign (size_t, size_t) */
static GTY (()) tree lineage_memalign_fndecl;

/* void * memcpy (dst, src, size_t) */
static GTY (()) tree lineage_memcpy_fndecl;

/* Helper for lineage_init: construct a decl with the given category,
   name, and type, mark it an external reference, and pushdecl it.  */
	static inline tree
lineage_make_builtin (enum tree_code category, const char *name, tree type)
{
	tree decl = build_decl (UNKNOWN_LOCATION, category, get_identifier (name), type);
	TREE_PUBLIC (decl) = 1;
	DECL_EXTERNAL (decl) = 1;
	lang_hooks.decls.pushdecl (decl);
	/* The decl was declared by the compiler.  */
	DECL_ARTIFICIAL (decl) = 1;
	/* And we don't want debug info for it.  */
	DECL_IGNORED_P (decl) = 1;
	return decl;
}

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

	void
lineage_fp_init (void)
{
	/* int lineage_icmp256_fndecl (int, v4df, v4df) */
	{
		tree lineage_icmp256_fndecl_fntype = 
			build_function_type_3 (integer_type_node,
					integer_type_node,
					v4df_type_node, v4df_type_node);

		lineage_icmp256_fndecl =
			lineage_make_builtin (FUNCTION_DECL, "icmp256",
					lineage_icmp256_fndecl_fntype);
	}

	{
		tree lineage_memalign_fntype =
			build_function_type_2 (ptr_type_node,
					size_type_node,
					size_type_node);

		lineage_memalign_fndecl =
			lineage_make_builtin (FUNCTION_DECL, "memalign",
					lineage_memalign_fntype);
	}

	{
		tree lineage_memcpy_fntype =
			build_function_type_3 (ptr_type_node,
					ptr_type_node,
					ptr_type_node,
					size_type_node);

		lineage_memcpy_fndecl =
			lineage_make_builtin (FUNCTION_DECL, "memcpy",
					lineage_memcpy_fntype);
	}

}

#undef build_function_type_3
#undef build_function_type_2

static void
lineage_fp_xfn_xform_fn_gimple_assign(gimple_stmt_iterator *gsi, gimple stmt)
{
	location_t location = gimple_location (stmt);

	switch (gimple_num_ops (stmt))
	{
		case 3:
		{
			enum tree_code op_code;
			tree op0, op1, op2;

			op0 = gimple_assign_lhs (stmt);
			op1 = gimple_assign_rhs1 (stmt);
			op2 = gimple_assign_rhs2 (stmt);
			op_code = gimple_assign_rhs_code (stmt);

			fprintf (stderr, "\tCase 3: EXPR: %s [%ld]=[%ld][%ld]\n", tree_code_name[op_code], 
					TYPE_SIZE_INT (op0), TYPE_SIZE_INT (op1), TYPE_SIZE_INT (op2));

			if (op_code == LT_EXPR || op_code == LE_EXPR
					|| op_code == GT_EXPR || op_code == GE_EXPR
					|| op_code == NE_EXPR || op_code == EQ_EXPR)
			{
				gimple_seq pre_seq = NULL;

				if (TREE_CODE (TREE_TYPE (op1)) == VECTOR_TYPE && TYPE_SIZE_INT (op1) == 256)
				{
					tree vlhs = op1;
					tree vrhs = op2;

					tree lhs;
					tree rhs;

					gcc_assert (TREE_CODE (TREE_TYPE (op2)) == VECTOR_TYPE);
					gcc_assert (TYPE_SIZE_INT (op2) == 256);

					/* lhs */
					{
						tree vlhs_ptr;
						tree lhs_ptr;
						tree t;
						gimple g;

						lhs = create_tmp_var (double_type_node, SHADOW_ID_PREFIX("__lhs", ""));
						DECL_ALIGN (lhs) = (32) * BITS_PER_UNIT;
						DECL_USER_ALIGN (lhs) = 1;

						vlhs_ptr = build1 (ADDR_EXPR,
								build_pointer_type (v4df_type_node), unshare_expr (vlhs));

						lhs_ptr = create_tmp_var (double_ptr_type_node, SHADOW_ID_PREFIX("__lhs", "_ptr"));

						t = fold_build1 (CONVERT_EXPR, double_ptr_type_node, vlhs_ptr);
						gimplify_expr (&t, &pre_seq, &pre_seq, is_gimple_reg_rhs, fb_rvalue);
						g = gimple_build_assign (lhs_ptr, t);
						gimple_set_location (g, location);
						gimple_seq_add_stmt (&pre_seq, g);

						t = build1 (INDIRECT_REF, double_type_node, lhs_ptr);
						gimplify_expr (&t, &pre_seq, &pre_seq, is_gimple_reg_rhs, fb_rvalue);
						g = gimple_build_assign (lhs, t);
						gimple_set_location (g, location);
						gimple_seq_add_stmt (&pre_seq, g);
					}

					/* rhs */
					{
						tree vrhs_ptr;
						tree rhs_ptr;
						tree t;
						gimple g;

						rhs = create_tmp_var (double_type_node, SHADOW_ID_PREFIX("__rhs", ""));
						DECL_ALIGN (rhs) = (32) * BITS_PER_UNIT;
						DECL_USER_ALIGN (rhs) = 1;

						vrhs_ptr = build1 (ADDR_EXPR,
								build_pointer_type (v4df_type_node), unshare_expr (vrhs));

						rhs_ptr = create_tmp_var (double_ptr_type_node, SHADOW_ID_PREFIX("__rhs_", "ptr"));

						t = fold_build1 (CONVERT_EXPR, double_ptr_type_node, vrhs_ptr);
						gimplify_expr (&t, &pre_seq, &pre_seq, is_gimple_reg_rhs, fb_rvalue);
						g = gimple_build_assign (rhs_ptr, t);
						gimple_set_location (g, location);
						gimple_seq_add_stmt (&pre_seq, g);

						t = build1 (INDIRECT_REF, double_type_node, rhs_ptr);
						gimplify_expr (&t, &pre_seq, &pre_seq, is_gimple_reg_rhs, fb_rvalue);
						g = gimple_build_assign (rhs, t);
						gimple_set_location (g, location);
						gimple_seq_add_stmt (&pre_seq, g);
					}

					/* Make the comparison and copy the result back to the LHS. */
					{
						tree t;
						gimple g;

						t = fold_build2 (op_code, boolean_type_node, lhs, rhs);
						gimplify_expr (&t, &pre_seq, &pre_seq, is_gimple_reg_rhs, fb_rvalue);
						g = gimple_build_assign (op0, t);
						gimple_set_location (g, location);

						gsi_replace (gsi, g, false);
					}
				}

				/* Accumulate the assignment.  */
				if (pre_seq)
				{
					/* Append to the mainline. */
					{
						gimple g;
						gimple_seq seq2 = NULL;

						g = gimple_build_bind (NULL, pre_seq, NULL);
						gimple_seq_add_stmt (&seq2, g);
						gsi_insert_seq_before (gsi, seq2, GSI_SAME_STMT);
					}

					/* Remove the original assignment. */
					/* NOTE: changed from remove to replace above. Otherwise the gsi pointer
					 * will be set to the next statement, which will thus be skipped.  */
				}
			}

			break;
		}

		case 2:
		default:
		{
			break;
		}
	}

	return;
}

static void
lineage_fp_xfn_xform_fn_gimple_call (gimple_stmt_iterator *gsi, gimple stmt)
{

	tree fndecl = gimple_call_fndecl (stmt);
	const char *callee_name;

	/* Function pointer, the callee is VAR_DECL instead of ADDR_EXPR->FUNCTION_DECL */
	if (fndecl == NULL_TREE)
	{
		tree addr = gimple_call_fn (stmt);
		callee_name = ID_PTR_NAME (addr);
	}
	else
	{
		callee_name = ID_PTR_NAME (fndecl);
	}

	/* Do nothing to gfortran_ functions. */
	if (!strncmp (callee_name, "_gfortran_", 10))
	{
		return;
	}

	if (!strcmp (callee_name, "malloc") || !strcmp (callee_name, "__builtin_malloc"))
	{
		/* Change it to aligned malloc */
		/* memalign (alignment, size) */
		tree sz = gimple_call_arg (stmt, 0);
		tree alignment = build_int_cst (NULL_TREE, 32);
		gimple fncall;

		fncall = gimple_build_call (lineage_memalign_fndecl, 2,
				alignment, sz);

		gimple_call_set_lhs (fncall, gimple_call_lhs (stmt));

		gsi_replace (gsi, fncall, true);

		return;
	}

	if (!strcmp (callee_name, "calloc") || !strcmp (callee_name, "__builtin_calloc"))
	{
		gcc_unreachable ();
	}

	if (!strcmp (callee_name, "realloc") || !strcmp (callee_name, "__builtin_realloc"))
	{
		tree sz = gimple_call_arg (stmt, 1);
		tree src = gimple_call_arg (stmt, 0);
		tree dst = gimple_call_lhs (stmt);
		tree alignment = build_int_cst (NULL_TREE, 32);
		gimple fncall;

		fncall = gimple_build_call (lineage_memalign_fndecl, 2,
				alignment, sz);

		gimple_call_set_lhs (fncall, dst);

		gsi_replace (gsi, fncall, true);

		/* memcpy from old ptr to new address */
		fncall = gimple_build_call (lineage_memcpy_fndecl, 3,
				dst, src, sz);

		gsi_insert_after (gsi, fncall, GSI_NEW_STMT);

		return;
	}

	/* Checking for real*8/4 type args. */
	{
		size_t i;

		for (i = 0; i < gimple_call_num_args (stmt); i++)
		{
			tree arg = gimple_call_arg (stmt, i);

			if (POINTER_TYPE_P (TREE_TYPE (arg)))
			{
				arg = TREE_TYPE (arg);
			}
			fprintf (stderr, "%lu: %s\n", i, tree_code_name[TREE_CODE (TREE_TYPE (arg))]);

			if (TREE_CODE (TREE_TYPE (arg)) == REAL_TYPE)
			{
				fprintf (stderr, "WARNING: Argument %lu is of REAL_TYPE.\n", i);
			}
		}
	}

	return;
}


/* Process every variable and every statement mentioned in BIND_EXPRs.  */
static tree
lineage_xfn_xform_fn (gimple_stmt_iterator *gsi,
		bool *handled_operands_p ATTRIBUTE_UNUSED,
		struct walk_stmt_info *wi ATTRIBUTE_UNUSED)
{
	gimple stmt = gsi_stmt (*gsi);
	location_t location = gimple_location (stmt);

	fprintf (stderr, "\n-- %s\n", 
			gimple_code_name[(int) gimple_code (stmt)]); 

	if (gimple_code (stmt) != GIMPLE_BIND && 
		gimple_code (stmt) != GIMPLE_TRY) 
	{
		//debug_gimple_stmt (stmt);
	}

	switch (gimple_code (stmt)) {
		case GIMPLE_BIND:
		{
			break;
		}

		case GIMPLE_ASSIGN:
		{
			//lineage_fp_xfn_xform_fn_gimple_assign (gsi, stmt);
			break;
		}

		case GIMPLE_CALL:
		{
			//lineage_fp_xfn_xform_fn_gimple_call (gsi, stmt);
			break;
		}

		case GIMPLE_COND:
		{
			/* 
			 * We need to check all the elements in the vector, 
			 * unless only -flineage-fp is specified. 
			 */
			if (flag_lineage) {
				enum tree_code op_code;
				tree left;

				left = gimple_cond_lhs (stmt);
				op_code = gimple_cond_code (stmt);

				fprintf (stderr, "[%s][%s]\n", tree_code_name[op_code], 
						tree_code_name[TREE_CODE (TREE_TYPE (left))]);

				if (TREE_CODE (TREE_TYPE (left)) == VECTOR_TYPE && 
					TYPE_SIZE_INT (left) == 256)
				{
					lineage_patch_predicate256 (gsi, stmt);
				}
			} else {
				enum tree_code op_code;
				tree left, right;
				gimple_seq pre_seq = NULL;

				left = gimple_cond_lhs (stmt);
				right = gimple_cond_rhs (stmt);
				op_code = gimple_cond_code (stmt);

				fprintf (stderr, "[%s][%s]\n", tree_code_name[op_code], 
						tree_code_name[TREE_CODE (TREE_TYPE (left))]);

				if (TREE_CODE (TREE_TYPE (left)) == VECTOR_TYPE && 
					TYPE_SIZE_INT (left) == 256)
				{
					tree vlhs = left;
					tree vrhs = right;

					tree lhs;
					tree rhs;

					/* lhs */
					{
						tree vlhs_ptr;
						tree lhs_ptr;
						tree t;
						gimple g;

						lhs = create_tmp_var (double_type_node, 
								SHADOW_ID_PREFIX("__lhs", ""));
						DECL_ALIGN (lhs) = (32) * BITS_PER_UNIT;
						DECL_USER_ALIGN (lhs) = 1;

						vlhs_ptr = build1 (ADDR_EXPR,
								build_pointer_type (v4df_type_node), 
								unshare_expr (vlhs));

						lhs_ptr = create_tmp_var (double_ptr_type_node, 
								SHADOW_ID_PREFIX("__lhs", "_ptr"));

						t = fold_build1 (CONVERT_EXPR, 
								double_ptr_type_node, vlhs_ptr);
				
						gimplify_expr (&t, &pre_seq, &pre_seq, 
								is_gimple_reg_rhs, fb_rvalue);
					
						g = gimple_build_assign (lhs_ptr, t);
						gimple_set_location (g, location);
						gimple_seq_add_stmt (&pre_seq, g);

						t = build1 (INDIRECT_REF, double_type_node, lhs_ptr);
						
						gimplify_expr (&t, &pre_seq, &pre_seq, 
								is_gimple_reg_rhs, fb_rvalue);
						
						g = gimple_build_assign (lhs, t);
						gimple_set_location (g, location);
						gimple_seq_add_stmt (&pre_seq, g);
					}

					/* rhs */
					{
						tree vrhs_ptr;
						tree rhs_ptr;
						tree t;
						gimple g;

						rhs = create_tmp_var (double_type_node, 
								SHADOW_ID_PREFIX("__rhs", ""));
						DECL_ALIGN (rhs) = (32) * BITS_PER_UNIT;
						DECL_USER_ALIGN (rhs) = 1;

						vrhs_ptr = build1 (ADDR_EXPR,
								build_pointer_type (v4df_type_node), 
								unshare_expr (vrhs));

						rhs_ptr = create_tmp_var (double_ptr_type_node, 
								SHADOW_ID_PREFIX("__rhs_", "ptr"));

						t = fold_build1 (CONVERT_EXPR, 
								double_ptr_type_node, vrhs_ptr);
						gimplify_expr (&t, &pre_seq, &pre_seq, 
								is_gimple_reg_rhs, fb_rvalue);
						g = gimple_build_assign (rhs_ptr, t);
						gimple_set_location (g, location);
						gimple_seq_add_stmt (&pre_seq, g);

						t = build1 (INDIRECT_REF, double_type_node, rhs_ptr);
						gimplify_expr (&t, &pre_seq, &pre_seq, 
								is_gimple_reg_rhs, fb_rvalue);
						g = gimple_build_assign (rhs, t);
						gimple_set_location (g, location);
						gimple_seq_add_stmt (&pre_seq, g);
					}

					gimple_cond_set_condition (stmt, op_code, lhs, rhs);

				}

				/* Accumulate the call.  */
				if (pre_seq)
				{
					/* Append to the mainline. */
					{
						gimple g;
						gimple_seq seq2 = NULL;

						g = gimple_build_bind (NULL, pre_seq, NULL);
						gimple_seq_add_stmt (&seq2, g);
						gsi_insert_seq_before (gsi, seq2, GSI_SAME_STMT);
					}

					/* It should rarely happen to insert instructions AFTER the branch. */
				}

			}
			break;
		}

		case GIMPLE_LABEL:
		{
			/* fprintf (stderr, "\n-- %s\n", gimple_code_name[(int) gimple_code (stmt)]); */
			break;
		}

		default:
			/* fprintf (stderr, "\n-- %s\n", gimple_code_name[(int) gimple_code (stmt)]); */
			break;
	}

	return NULL_TREE;
}

/* 
 * Perform the object lifetime tracking mudflap transform on the given 
 * function tree. The tree is mutated in place, with possibly copied 
 * subtree nodes.
 */
static void
lineage_xform_fn (gimple_seq fnbody, tree fnparams)
{
	struct lineage_xform_decls_data d;
	struct walk_stmt_info wi;
	struct pointer_set_t *pset;

	pset = pointer_set_create ();
	d.param_decls = fnparams;
	memset (&wi, 0, sizeof (wi));
	wi.info = (void *) &d;
	wi.pset = pset;
	walk_gimple_seq (fnbody, lineage_xfn_xform_fn, NULL, &wi);
	pointer_set_destroy (pset);

}


	static unsigned int
do_lineage_fp (void)
{
#if 0
	struct gimplify_ctx gctx;
	const char *decl_name = lang_hooks.decl_printable_name (current_function_decl, 2);

	fprintf (stderr, ";; ========================\n");
	fprintf (stderr, ";; [do_lineage_fp] %s\n", decl_name);
	fprintf (stderr, ";; ========================\n");

	/* Skip built-in _mm intrinsic functions */
	if (!strncmp (decl_name, "_mm", 3))
	{
		fprintf (stderr, "[%s] skipped.\n", decl_name);

		return 0;
	}

	push_gimplify_context (&gctx);

	lineage_xform_fn (gimple_body (current_function_decl),
			DECL_ARGUMENTS (current_function_decl));

	pop_gimplify_context (
			gimple_seq_first_stmt (gimple_body (current_function_decl)));
#endif
	return 0;
}


/* The pass gate. */
	static bool
gate_lineage_fp (void)
{
	return (flag_lineage_fp != 0 || flag_lineage != 0);
}

struct gimple_opt_pass pass_lineage_fp =
{
	{
		GIMPLE_PASS,
		"lineagefp",                 /* name */
		gate_lineage_fp,              /* gate */
		do_lineage_fp,                /* execute */
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
