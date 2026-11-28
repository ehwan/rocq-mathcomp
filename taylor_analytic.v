From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype derive sequences.
From mathcomp Require Import arithmetic_tactic.

Require Import taylor_poly taylor_expansion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition analytic_derivative_bound (R : realType) (f : R -> R) (a b : R) : Prop :=
  exists C : R,
    forall (k : nat), {in `[a, b], forall (x : R),
      `|f^`(k) x| <= C^+k.+1 * k`!%:R}.

Section analytic.
Context (R : realType).
Context (f : R -> R).
Context (F_Derivable : forall (k : nat) (x : R), derivable (derive1n k f) x 1).
Context (F_Analytic3 : forall (a b : R), analytic_derivative_bound f a b).

Theorem taylor_theorem2 (a x : R) :
  exists Radius : R,
    Radius > 0 -> `|x - a| < Radius ->
    (fun n => f x - taylor_sum f n a x) @\oo --> 0.
Proof.
have [C C_bound] : analytic_derivative_bound f (minr a x) (maxr a x).
- exact: F_Analytic3.
exists C^-1.
rewrite invr_gt0.
move=> C_pos.
rewrite -div1r.
rewrite ltr_pdivlMr // mulrC.
move=> xa_radius.

pose X_n (n : nat) := C * (C * `|x - a|)^+n.+1.
have X_cvgr : X_n @\oo --> 0.
- apply: cvgM0.
  + exact: cvg_cst.
  + rewrite cvg_shiftS.
    apply: cvg_expr.
    rewrite ger0_norm.
    * have norm_ge0 : 0 <= `|x - a|.
      -- exact: normr_ge0.
      by nra.
    exact: xa_radius.

pose taylor_interval := (`[minr a x, maxr a x]%R).
have a_in : a \in taylor_interval.
- by rewrite /taylor_interval in_itv /= ge_min le_max lexx.
have x_in : x \in taylor_interval.
- by rewrite /taylor_interval in_itv /= ge_min le_max lexx !orbT.
have remainder_range n :
    -X_n n <= f x - taylor_sum f n a x <= X_n n.
- have remainder_bound :
      `|f x - taylor_sum f n a x| <=
        (C^+n.+2 * n.+1`!%:R) / n.+1`!%:R * `|x - a|^+n.+1.
  + apply: taylor_expansion_bound.
    * exact: a_in.
    * move=> k _ y _.
      exact: F_Derivable.
    * exact: x_in.
    * move=> y y_in.
      apply: C_bound.
      by rewrite inE.
  move: remainder_bound.
  rewrite mulfK.
  + by rewrite pnatr_eq0 -lt0n fact_gt0.
  rewrite -ler_norml.
  by rewrite /X_n exprMn mulrA -exprS.
apply: squeeze_cvgr.
- apply: nearW.
  exact: remainder_range.
- rewrite -oppr0.
  apply: cvgN.
  exact: X_cvgr.
- exact: X_cvgr.
Qed.

End analytic.
