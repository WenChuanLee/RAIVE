
;; Function main (main, funcdef_no=812, return=integer_type, decl_uid=6567, cgraph_uid=812) (executed once)

;; 1 loops found
;;
;; Loop 0
;;  header 0, latch 1
;;  depth 0, outer -1
;;  nodes: 0 1 2 3 4 5 6 7 8
;; 2 succs { 6 3 }
;; 3 succs { 4 5 }
;; 4 succs { 5 }
;; 5 succs { 6 7 }
;; 6 succs { 8 }
;; 7 succs { 8 }
;; 8 succs { 1 }
main ()
{
  __m256d res;
  double D.6692;
  double D.6691;
  vector(4) double res.1;
  _Bool D.6725;
  _Bool D.6724;
  int __rtn_v2.24;
  int __rtn_v1.23;
  vector(4) double a.22;
  vector(4) double res.18;
  double __lhs_v2.16;
  double __lhs_v1.15;
  int __rtn_v1.10;
  vector(4) double c.9;
  vector(4) double res.5;

<bb 2>:
  gimple_debug BIND <__A, 3.29123456791234502816223539412021636962890625e+2>
  gimple_debug BIND <a, NULL>
  gimple_debug BIND <__A, 3.291234567912343891293858177959918975830078125e+2>
  gimple_debug BIND <b, NULL>
  gimple_debug BIND <__A, 9.99999982451670044181213370393379591405391693115234375e-14>
  gimple_debug BIND <c, NULL>
  gimple_assign <vector_cst, res, { 8.5265128291212022304534912109375e-14, 1.42108547152020037174224853515625e-13, 1.136868377216160297393798828125e-13, 1.136868377216160297393798828125e-13 }, NULL>
  gimple_assign <vector_cst, res.5, { 8.5265128291212022304534912109375e-14, 1.42108547152020037174224853515625e-13, 1.136868377216160297393798828125e-13, 1.136868377216160297393798828125e-13 }, NULL>
  gimple_assign <vector_cst, c.9, { 9.99999982451670044181213370393379591405391693115234375e-14, 9.99999982451670044181213370393379591405391693115234375e-14, 9.99999982451670044181213370393379591405391693115234375e-14, 9.99999982451670044181213370393379591405391693115234375e-14 }, NULL>
  gimple_call <lineage_spawn, __rtn_v1.10_36, 0, 1, &res.5, &c.9, "../../../test/test1/test.c:36:5 res.1">
  gimple_debug BIND <D#2, &c.9>
  gimple_debug BIND <D#1, *D#2>
  gimple_debug BIND <c, D#1>
  gimple_cond <eq_expr, __rtn_v1.10_36, 1, NULL, NULL>
    goto <bb 6>;
  else
    goto <bb 3>;

<bb 3>:
  gimple_assign <var_decl, res.1_41, res, NULL>
  gimple_assign <ssa_name, res.18, res.1_41, NULL>
  gimple_assign <mem_ref, __lhs_v1.15_43, MEM[(double *)&res.18], NULL>
  gimple_assign <mem_ref, __lhs_v2.16_45, MEM[(double *)&res.18 + 8B], NULL>
  gimple_assign <vector_cst, a.22, { 3.29123456791234502816223539412021636962890625e+2, 3.29123456791234502816223539412021636962890625e+2, 3.29123456791234502816223539412021636962890625e+2, 3.29123456791234502816223539412021636962890625e+2 }, NULL>
  gimple_assign <gt_expr, D.6724_50, __lhs_v1.15_43, 3.29123456791234502816223539412021636962890625e+2>
  gimple_assign <nop_expr, __rtn_v1.23_51, D.6724_50, NULL>
  gimple_assign <gt_expr, D.6725_52, __lhs_v2.16_45, 3.29123456791234502816223539412021636962890625e+2>
  gimple_assign <nop_expr, __rtn_v2.24_53, D.6725_52, NULL>
  gimple_cond <ne_expr, __rtn_v1.23_51, __rtn_v2.24_53, NULL, NULL>
    goto <bb 4>;
  else
    goto <bb 5>;

<bb 4>:
  gimple_call <lineage_spawn, __rtn_v1.23_55, __rtn_v1.23_51, __rtn_v2.24_53, &res.18, &a.22, "../../../test/test1/test.c:36:14 res.1">
  gimple_debug BIND <D#4, &a.22>
  gimple_debug BIND <D#3, *D#4>
  gimple_debug BIND <a, D#3>

<bb 5>:
  # gimple_phi <__rtn_v1.23_3, __rtn_v1.23_51(3), __rtn_v1.23_55(4)>
  gimple_cond <eq_expr, __rtn_v1.23_3, 1, NULL, NULL>
    goto <bb 6>;
  else
    goto <bb 7>;

<bb 6>:
  gimple_assign <bit_field_ref, D.6691_62, BIT_FIELD_REF <res, 64, 64>, NULL>
  gimple_assign <bit_field_ref, D.6692_63, BIT_FIELD_REF <res, 64, 0>, NULL>
  gimple_call <printf, NULL, "T:%.17lf %.17lf\n", D.6692_63, D.6691_62>
  gimple_call <printf, NULL, "res:%lx\n", &res>
  gimple_call <__builtin_puts, NULL, &"true"[0]>
  goto <bb 8>;

<bb 7>:
  gimple_assign <bit_field_ref, D.6691_60, BIT_FIELD_REF <res, 64, 64>, NULL>
  gimple_assign <bit_field_ref, D.6692_61, BIT_FIELD_REF <res, 64, 0>, NULL>
  gimple_call <printf, NULL, "F:%.17lf %.17lf\n", D.6692_61, D.6691_60>
  gimple_call <printf, NULL, "res:%lx\n", &res>
  gimple_call <__builtin_puts, NULL, &"false"[0]>

<bb 8>:
  gimple_assign <constructor, res, {CLOBBER}, NULL>
  gimple_return <NULL>

}



;; Function _GLOBAL__sub_I_00099_0_main (_GLOBAL__sub_I_00099_0_main, funcdef_no=813, return=void_type, decl_uid=6771, cgraph_uid=0) (executed once)

;; 1 loops found
;;
;; Loop 0
;;  header 0, latch 1
;;  depth 0, outer -1
;;  nodes: 0 1 2
;; 2 succs { 1 }
_GLOBAL__sub_I_00099_0_main ()
{
<bb 2>:
  gimple_call <lineage_init, NULL>
  gimple_return <NULL>

}



;; Function _GLOBAL__sub_D_00099_1_main (_GLOBAL__sub_D_00099_1_main, funcdef_no=814, return=void_type, decl_uid=6777, cgraph_uid=788) (executed once)

;; 1 loops found
;;
;; Loop 0
;;  header 0, latch 1
;;  depth 0, outer -1
;;  nodes: 0 1 2
;; 2 succs { 1 }
_GLOBAL__sub_D_00099_1_main ()
{
<bb 2>:
  gimple_call <lineage_fini, NULL>
  gimple_return <NULL>

}


