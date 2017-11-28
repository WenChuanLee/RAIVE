
;; Function main (main, funcdef_no=812, return=integer_type, decl_uid=6567, cgraph_uid=812)

main ()
{
  long unsigned int * ptr;
  __m256d res;
  __m256d c;
  __m256d b;
  __m256d a;
  int i;
  double D.6692;
  double D.6691;
  vector(4) double res.1;
  __m256d res.0;
  vector(4) double * a.27;
  vector(4) double * res.26;
  _Bool __cmp.25;
  _Bool D.6725;
  _Bool D.6724;
  int __rtn_v2.24;
  int __rtn_v1.23;
  double * D.6721;
  vector(4) double a.22;
  double * __rhs_ptr.21;
  double __rhs_v2.20;
  double __rhs_v1.19;
  double * D.6716;
  vector(4) double res.18;
  double * __lhs_ptr.17;
  double __lhs_v2.16;
  double __lhs_v1.15;
  vector(4) double * c.14;
  vector(4) double * res.13;
  _Bool __cmp.12;
  _Bool D.6706;
  _Bool D.6705;
  int __rtn_v2.11;
  int __rtn_v1.10;
  double * D.6702;
  vector(4) double c.9;
  double * __rhs_ptr.8;
  double __rhs_v2.7;
  double __rhs_v1.6;
  double * D.6697;
  vector(4) double res.5;
  double * __lhs_ptr.4;
  double __lhs_v2.3;
  double __lhs_v1.2;
  vector(4) double __op0_vpatch.41;
  vector(4) double __op0_vpatch.40;
  double __op0_patch_neg.39;
  double __op0_patch.38;
  long unsigned int __op1_patch.37;
  double * __op1_patch_ptr.36;
  long unsigned int __op1_patch.35;
  long int __exp_delta.34;
  vector(4) double * __op1_copy.33;
  long unsigned int __op1_exp1.32;
  vector(4) double * res.31;
  __m256d res.30;
  long unsigned int __op0_exp0.29;
  vector(4) double __op1_copy.28;

  gimple_call <_mm256_set1_pd, a, 3.29123456791234502816223539412021636962890625e+2>
  gimple_call <_mm256_set1_pd, b, 3.291234567912343891293858177959918975830078125e+2>
  gimple_call <_mm256_set1_pd, c, 9.99999982451670044181213370393379591405391693115234375e-14>
  gimple_assign <var_decl, __op1_copy.28, a, NULL>
  gimple_assign <minus_expr, res.0, a, b>
  gimple_assign <var_decl, res.30, res.0, NULL>
  gimple_assign <addr_expr, res.31, &res.30, NULL>
  gimple_assign <mem_ref, __op0_exp0.29, MEM[(vector(4) double *)res.31], NULL>
  gimple_assign <bit_and_expr, __op0_exp0.29, __op0_exp0.29, 9218868437227405312>
  gimple_assign <addr_expr, __op1_copy.33, &__op1_copy.28, NULL>
  gimple_assign <mem_ref, __op1_exp1.32, MEM[(vector(4) double *)__op1_copy.33], NULL>
  gimple_assign <bit_and_expr, __op1_exp1.32, __op1_exp1.32, 9218868437227405312>
  gimple_assign <minus_expr, __exp_delta.34, __op1_exp1.32, __op0_exp0.29>
  gimple_cond <gt_expr, __exp_delta.34, 216172782113783808, <D.6738>, <D.6739>>
  gimple_label <<D.6738>>
  gimple_assign <plus_expr, __op1_patch.35, __op1_exp1.32, 18208053293458915328>
  gimple_assign <bit_and_expr, __op1_patch.35, __op1_patch.35, 9218868437227405312>
  gimple_assign <var_decl, __op1_patch.37, __op1_patch.35, NULL>
  gimple_assign <addr_expr, __op1_patch_ptr.36, &__op1_patch.37, NULL>
  gimple_assign <mem_ref, __op0_patch.38, *__op1_patch_ptr.36, NULL>
  gimple_assign <negate_expr, __op0_patch_neg.39, __op0_patch.38, NULL>
  gimple_assign <constructor, __op0_vpatch.40, {__op0_patch_neg.39, __op0_patch.38, 0.0, 0.0}, NULL>
  gimple_assign <var_decl, __op0_vpatch.41, __op0_vpatch.40, NULL>
  gimple_assign <plus_expr, res.0, res.0, __op0_vpatch.41>
  gimple_label <<D.6739>>
  GIMPLE_NOP
  gimple_assign <var_decl, res, res.0, NULL>
  gimple_assign <var_decl, res.1, res, NULL>
  gimple_assign <var_decl, res.5, res.1, NULL>
  gimple_assign <addr_expr, __lhs_ptr.4, &res.5, NULL>
  gimple_assign <mem_ref, __lhs_v1.2, *__lhs_ptr.4, NULL>
  gimple_assign <pointer_plus_expr, D.6697, __lhs_ptr.4, 8>
  gimple_assign <mem_ref, __lhs_v2.3, *D.6697, NULL>
  gimple_assign <var_decl, c.9, c, NULL>
  gimple_assign <addr_expr, __rhs_ptr.8, &c.9, NULL>
  gimple_assign <mem_ref, __rhs_v1.6, *__rhs_ptr.8, NULL>
  gimple_assign <pointer_plus_expr, D.6702, __rhs_ptr.8, 8>
  gimple_assign <mem_ref, __rhs_v2.7, *D.6702, NULL>
  gimple_assign <gt_expr, D.6705, __lhs_v1.2, __rhs_v1.6>
  gimple_assign <nop_expr, __rtn_v1.10, D.6705, NULL>
  gimple_assign <gt_expr, D.6706, __lhs_v2.3, __rhs_v2.7>
  gimple_assign <nop_expr, __rtn_v2.11, D.6706, NULL>
  gimple_assign <eq_expr, __cmp.12, __rtn_v1.10, __rtn_v2.11>
  gimple_cond <eq_expr, __cmp.12, 0, <D.6708>, <D.6709>>
  gimple_label <<D.6708>>
  gimple_call <lineage_spawn, __rtn_v1.10, __rtn_v1.10, __rtn_v2.11, &res.5, &c.9, "../../../test/test1/test.c:36:5 res.1">
  gimple_assign <addr_expr, res.13, &res.5, NULL>
  gimple_assign <mem_ref, res.1, *res.13, NULL>
  gimple_assign <addr_expr, c.14, &c.9, NULL>
  gimple_assign <mem_ref, c, *c.14, NULL>
  gimple_label <<D.6709>>
  gimple_cond <eq_expr, __rtn_v1.10, 1, <D.6686>, <D.6690>>
  gimple_label <<D.6690>>
  gimple_assign <var_decl, res.1, res, NULL>
  gimple_assign <var_decl, res.18, res.1, NULL>
  gimple_assign <addr_expr, __lhs_ptr.17, &res.18, NULL>
  gimple_assign <mem_ref, __lhs_v1.15, *__lhs_ptr.17, NULL>
  gimple_assign <pointer_plus_expr, D.6716, __lhs_ptr.17, 8>
  gimple_assign <mem_ref, __lhs_v2.16, *D.6716, NULL>
  gimple_assign <var_decl, a.22, a, NULL>
  gimple_assign <addr_expr, __rhs_ptr.21, &a.22, NULL>
  gimple_assign <mem_ref, __rhs_v1.19, *__rhs_ptr.21, NULL>
  gimple_assign <pointer_plus_expr, D.6721, __rhs_ptr.21, 8>
  gimple_assign <mem_ref, __rhs_v2.20, *D.6721, NULL>
  gimple_assign <gt_expr, D.6724, __lhs_v1.15, __rhs_v1.19>
  gimple_assign <nop_expr, __rtn_v1.23, D.6724, NULL>
  gimple_assign <gt_expr, D.6725, __lhs_v2.16, __rhs_v2.20>
  gimple_assign <nop_expr, __rtn_v2.24, D.6725, NULL>
  gimple_assign <eq_expr, __cmp.25, __rtn_v1.23, __rtn_v2.24>
  gimple_cond <eq_expr, __cmp.25, 0, <D.6727>, <D.6728>>
  gimple_label <<D.6727>>
  gimple_call <lineage_spawn, __rtn_v1.23, __rtn_v1.23, __rtn_v2.24, &res.18, &a.22, "../../../test/test1/test.c:36:14 res.1">
  gimple_assign <addr_expr, res.26, &res.18, NULL>
  gimple_assign <mem_ref, res.1, *res.26, NULL>
  gimple_assign <addr_expr, a.27, &a.22, NULL>
  gimple_assign <mem_ref, a, *a.27, NULL>
  gimple_label <<D.6728>>
  gimple_cond <eq_expr, __rtn_v1.23, 1, <D.6686>, <D.6687>>
  gimple_label <<D.6686>>
  gimple_assign <bit_field_ref, D.6691, BIT_FIELD_REF <res, 64, 64>, NULL>
  gimple_assign <bit_field_ref, D.6692, BIT_FIELD_REF <res, 64, 0>, NULL>
  gimple_call <printf, NULL, "T:%.17lf %.17lf\n", D.6692, D.6691>
  gimple_call <printf, NULL, "res:%lx\n", &res>
  gimple_call <__builtin_puts, NULL, &"true"[0]>
  gimple_goto <<D.6688>>
  gimple_label <<D.6687>>
  gimple_assign <bit_field_ref, D.6691, BIT_FIELD_REF <res, 64, 64>, NULL>
  gimple_assign <bit_field_ref, D.6692, BIT_FIELD_REF <res, 64, 0>, NULL>
  gimple_call <printf, NULL, "F:%.17lf %.17lf\n", D.6692, D.6691>
  gimple_call <printf, NULL, "res:%lx\n", &res>
  gimple_call <__builtin_puts, NULL, &"false"[0]>
  gimple_label <<D.6688>>
  gimple_assign <constructor, res, {CLOBBER}, NULL>
  gimple_return <NULL>
}



;; Function _mm256_set1_pd (_mm256_set1_pd, funcdef_no=788, return=vector_type, decl_uid=6304, cgraph_uid=788)

_mm256_set1_pd (double __A)
{
  __m256d D.6747;

  gimple_assign <constructor, D.6747, {__A, __A, __A, __A}, NULL>
  gimple_goto <<D.6748>>
  gimple_label <<D.6748>>
  gimple_return <D.6747>
}



;; Function _GLOBAL__sub_I_00099_0_main (_GLOBAL__sub_I_00099_0_main, funcdef_no=813, return=void_type, decl_uid=6771, cgraph_uid=0)

_GLOBAL__sub_I_00099_0_main ()
{
  gimple_call <lineage_init, NULL>
  gimple_return <NULL>
}



;; Function _GLOBAL__sub_D_00099_1_main (_GLOBAL__sub_D_00099_1_main, funcdef_no=814, return=void_type, decl_uid=6777, cgraph_uid=788)

_GLOBAL__sub_D_00099_1_main ()
{
  gimple_call <lineage_fini, NULL>
  gimple_return <NULL>
}


