From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau derive sequences realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Import Num.Def Num.Theory.

(* From Coq Require Import Reals. *)
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section sequence.
Context (R: realType).
Definition geometric_arithmetic (a r: R) := [sequence a*(r^+n)*+n]_n.

Theorem cvg_geometric_arithmetic (a r: R) :
  `|r| < 1 -> geometric_arithmetic a r @\oo --> 0.
Proof.
move=> radius.
(* cbn. *)
(* apply: norm_cvg0. *)
pose q:R := (`|r| + 1)/2.
pose t:R := `|r| / q.
pose C:R := `|a| / ( 1 - t ).

have rnorm_ge0:= (normr_ge0 r).

have q_gt_rnorm: q > `|r|.
- rewrite /q.
  by lra.

have q_lt1: q < 1.
- rewrite /q.
  by lra.

have t_ge0: t >= 0.
- rewrite /t.
  rewrite ler_pdivlMr.
  lra.
  by lra.

have t_lt1: t < 1.
- rewrite /t.
  rewrite ltr_pdivrMr.
  lra.
  by lra.

have tn_ge0 (n: nat): t^+n >= 0.
- by rewrite exprn_ge0 //=.

have tn_le (n: nat): t^+n.+1 <= t^+n.
- rewrite exprS.
  have tn_nonneg := tn_ge0 n.
  by nra.

have r_eq_tq: `|r| = t * q.
- rewrite /t.
  rewrite divfK //=.
  by lra.

(* for squeeze theorem *)
have cvg_X: C * q^+n @[n --> \oo] --> 0.
- rewrite -(mulr0 C).
  apply: cvgMl_tmp.
  apply: cvg_expr.
  rewrite ger0_norm //=.
  by lra.

have cvg_nX: -(C * q^+n) @[n --> \oo] --> 0.
- rewrite -oppr0.
  apply: cvgN.
  by apply: cvg_X.

(* squeeze theorem le_trans *)
have LE0 (n: nat): geometric_arithmetic a r n <= `|a| * `|r^+n| *+ n.
- rewrite /geometric_arithmetic.
  cbn.
  rewrite -normrM.
  rewrite -normrMn.
  by apply: ler_norm.

have LE1 (n: nat): `|a| * `|r^+n| *+ n <= `|a| * (\sum_(i < n) t^+i) * q^+n.
- rewrite -mulrA -mulrnAr.
  apply: ler_wpM2l.
  + by apply: normr_ge0.
  rewrite normrX r_eq_tq exprMn -mulrnAl.
  apply: ler_wpM2r.
  + apply: exprn_ge0. 
    by lra.

  elim: n.
  + rewrite expr0.
    by rewrite big_ord0.
  + move=> n IH.
    apply: le_trans.
    * apply: (_: t^+n.+1 *+ n.+1 <= t^+n *+ (n.+1)).
      - by rewrite ler_pMn2r //=.
    * rewrite big_ord_recr //=.
      rewrite mulrSr.
      rewrite lerD2r.
      by exact: IH.

have geometric_series_mult (n: nat): (\sum_(i < n)  t ^+ i) * (1 - t) = 1 - t^+n.
- elim: n.
  + rewrite big_ord0 //=.
    rewrite expr0.
    by ring.
  + move=> n IH.
    rewrite big_ord_recr //=.
    rewrite mulrDl.
    rewrite IH.
    rewrite exprSr.
    by ring.

have LE2 (n: nat): `|a| * (\sum_(i < n) t^+i) * q^+n <= C * q^+n.
- rewrite ler_wpM2r //=.
  + apply: exprn_ge0.
    by lra.
  rewrite /C ler_wpM2l //=.

  rewrite -div1r ler_pdivlMr.
  + by lra.

  have tn_ge0':= (tn_ge0 n).
  rewrite geometric_series_mult.
  by lra.

have LE3 (n: nat): -(`|a| * `|r^+n| *+ n) <= geometric_arithmetic a r n.
- rewrite /geometric_arithmetic.
  cbn.
  rewrite -normrM.
  rewrite -normrMn.
  by apply: lerNnormlW.


have LE4 (n: nat): -(`|a| * (\sum_(i < n) t^+i) * q^+n) <= -(`|a| * `|r^+n| *+ n).
- rewrite lerN2.
  by apply: LE1.


have LE5 (n: nat): -(C * q^+n) <= -(`|a| * (\sum_(i < n) t^+i) * q^+n).
- rewrite lerN2.
  by apply: LE2.

apply: squeeze_cvgr.
- apply: nearW.
  move=> n.
  apply /andP.
  split.
  + apply: le_trans.
    * apply: le_trans.
      - by apply: LE5.
      - by apply: LE4.
    * by apply: LE3.
  + apply: le_trans.
    * apply: le_trans.
      - by apply: LE0.
      - by apply: LE1.
    * by apply: LE2.
- by apply: cvg_nX.
- by apply: cvg_X.
Qed.

End sequence.
