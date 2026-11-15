From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau derive sequences
  realfun.

From mathcomp Require Import arithmetic_tactic.

Require Import taylor_poly taylor_remainder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Import Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* Open Set D *)
(* forall compact set K=[a,b] \subset D *)
Definition analytic_derivative_bound (R : realType) (f : R -> R) (a b : R) :=
  exists C : R,
    forall (k : nat), {in `[a, b], forall (x : R),
      `|f^`(k) x| <= C^+k.+1 * k`!%:R}.

Section analytic.
Context (R : realType).
Context (f : R -> R).
Context (F_Derivable : forall (k : nat) (x : R), derivable (derive1n k f) x 1).
Context (F_Analytic3 : forall (a b : R), analytic_derivative_bound f a b).

(* C * |x - a| < 1 *)
Theorem taylor_theorem2 (a x : R) :
  exists Radius : R,
    Radius > 0 -> `|x - a| < Radius ->
    (fun n => f x - taylor_sum f n a x) @\oo --> 0.
Proof.
have [C H_C] := F_Analytic3 (minr x a) (maxr x a).
exists (1 / C).
rw div1r invr_gt0.
move=> C_GT0.
rw -div1r.
rw ltr_pdivlMr.
- exact: C_GT0.
rw mulrC.
move=> xa_radius.

pose X_n := fun n : nat => C * (C * `|x - a|)^+n.+1.
have X_cvgr : X_n @\oo --> 0.
- rw -(mulr0 C).
  apply: cvgMl_tmp.
  rw cvg_shiftS.
  apply: cvg_expr.
  rw ger0_norm.
  + have := normr_ge0 (x - a).
    by nra.
  by lra.

have remainder_range n :
    -X_n n <= f x - taylor_sum f n a x <= X_n n.
- have [xi xi_in remainder_eq] :=
    @taylor_remainder_lagrange R f n x (fun k _ => @F_Derivable k) a.
  have fact_pos : 0 < (n.+1)`!%:R :> R.
  + by rw ltr0n fact_gt0.
  rw -ler_norml.
  rw remainder_eq.
  rw normrM normf_div normrX.
  rw (gtr0_norm fact_pos).
  rw /X_n.
  rw exprMn.
  rw mulrA -exprS.
  apply: ler_wpM2r.
  + apply: exprn_ge0.
    exact: normr_ge0.
  rw ler_pdivrMr.
  + exact: fact_pos.
  apply: H_C.
  by rw inE.
apply: squeeze_cvgr.
- apply: nearW.
  exact: remainder_range.
- rw -oppr0.
  apply: cvgN.
  exact: X_cvgr.
- exact: X_cvgr.
Qed.

End analytic.
