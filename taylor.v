From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype derive realfun.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic zify.

Require Import taylor_poly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section taylor_theorem.
Context (R : realType) (f : R -> R) (a : R).

(* f is k times differentiable. *)
Context (k : nat).
Context (k_gt0 : (0 < k)%N).
Context (F_Derivable : derivable (f^`(k.-1)) a 1).
Context (F_Derivable_Near : forall (d : nat), (d < k.-1)%N ->
  \forall x \near a, derivable f^`(d) x 1).

Local Notation "'T_' '(' d ';' n ')'" := (taylor_sum (f^`(d)) n a).

Local Lemma derive_iterated_taylor_sumS (d n : nat) (x : R) :
  'D_1 T_(d; n.+1) x = T_(d.+1; n) x.
Proof.
rewrite derive_taylor_sumS.
by rewrite -derive1nS.
Qed.

Local Definition taylor_remainder_peano (d n : nat) (x : R) : R :=
  (f^`(d) x - T_(d; n) x) / (x - a)^+n.
Local Notation "'h_' '(' d ';' n ')'" := (taylor_remainder_peano d n).

Local Lemma taylor_remainder_peano_center (d n : nat) : h_(d; n) a = 0.
Proof.
rewrite /taylor_remainder_peano.
rewrite taylor_sum_center.
by lra.
Qed.

Local Lemma cvg_iterated_derive_increment (d : nat) :
  derivable (f^`(d)) a 1 ->
  (f^`(d) (a + h) - f^`(d) a) / h @[h --> (0 : R)^'] --> f^`(d.+1) a.
Proof.
move=> df.
rewrite derive1nS derive1E.
rewrite (_ : (fun h : R => (f^`(d) (a + h) - f^`(d) a) / h) =
  (fun h : R => h^-1 *: ((f^`(d) \o shift a) (h *: 1) - f^`(d) a))).
- apply: eq_fun.
  move=> h.
  rewrite /comp /shift.
  rewrite scaler1.
  rewrite [h + a]addrC.
  rewrite /GRing.scale /=.
  by rewrite mulrC.
exact: df.
Qed.

Local Lemma cvg_iterated_derive (d : nat) :
  derivable (f^`(d)) a 1 ->
  (f^`(d) x - f^`(d) a) / (x - a) @[x --> a^'] --> f^`(d.+1) a.
Proof.
move=> df.
rewrite (_ : (fun x : R => (f^`(d) x - f^`(d) a) / (x - a)) =
  (fun h : R => (f^`(d) (a + h) - f^`(d) a) / h) \o (fun x : R => x - a)).
- apply: eq_fun.
  move=> x.
  by rewrite /comp subrKC.
have shift_cvgr : x - a @[x --> a^'] --> (0 : R)^'.
- rewrite /dnbhs.
  apply/cvg_to_withinP.
  split.
  + rewrite -(subrr a).
    apply: cvgB.
    * exact: nbhs_dnbhs.
    * exact: cvg_cst.
  + change (\forall x \near a^', x - a != 0).
    rewrite /dnbhs near_withinE.
    apply: nearW.
    move=> x.
    by rewrite subr_eq0.
apply: cvg_comp.
- exact: shift_cvgr.
- apply: cvg_iterated_derive_increment.
  exact: df.
Qed.

(* A first-order remainder follows directly from differentiability. *)
Local Lemma cvg_taylor_remainder_peano1 (d : nat) :
  derivable (f^`(d)) a 1 -> h_(d; 1) x @[x --> a^'] --> 0.
Proof.
move=> df.
pose Q (x : R) := (f^`(d) x - f^`(d) a) / (x - a) - f^`(d.+1) a.
rewrite (_ : h_(d; 1) @ a^' = Q @ a^').
- apply: near_eq_cvg_eq.
  rewrite /dnbhs near_withinE.
  apply: nearW.
  move=> x xa.
  have sub_neq : x - a != 0.
  + by rewrite subr_eq0.
  rewrite /Q /taylor_remainder_peano.
  rewrite taylor_sumS taylor_sum0.
  rewrite /taylor_term !fctE.
  rewrite derive1n1 -derive1nS.
  rewrite factS fact0 /=.
  rewrite !expr1.
  by field.
rewrite /Q.
rewrite -[X in _ --> X](subrr (f^`(d.+1) a)).
apply: cvgB.
- apply: cvg_iterated_derive.
  exact: df.
- exact: cvg_cst.
Qed.

(* One L'Hopital step moves one derivative into the Taylor degree. *)
Local Lemma cvg_taylor_remainder_peano_step (d n : nat) :
  (\forall x \near a, derivable (f^`(d)) x 1) ->
  h_(d.+1; n) x @[x --> a^'] --> 0 ->
  h_(d; n.+1) x @[x --> a^'] --> 0.
Proof.
move=> fd cvg_next.
move/nbhs_normP: fd => [r /= r_gt0 fd_ball].
pose I := (`]a - r, a + r[%R).
pose N := f^`(d) - T_(d; n.+1).
pose D := (id - cst a)^+n.+1.
pose dN (x : R) := f^`(d.+1) x - T_(d.+1; n) x.
pose dD (x : R) := n.+1%:R * (x - a)^+n.
have a_in : a \in I.
- rewrite /I in_itv /=.
  by lra.
have fd_itv (x : R) : x \in I -> derivable (f^`(d)) x 1.
- move=> x_in_range.
  apply: fd_ball.
  rewrite /ball_ /=.
  rewrite ltr_distlC.
  move: x_in_range.
  by rewrite /I in_itv /=.
have deriv_N (x : R) : x \in [set` I] `\ a -> is_derive x 1 N (dN x).
- rewrite inE.
  move=> [x_in _].
  have fx_derivable : derivable (f^`(d)) x 1.
  + apply: fd_itv.
    exact: x_in.
  rewrite /N /dN.
  apply: DeriveDef.
  + apply: derivableB.
    * exact: fx_derivable.
    * exact: taylor_sum_derivable.
  + rewrite deriveB //=.
    rewrite -derive1E -derive1nS.
    by rewrite derive_iterated_taylor_sumS.
have deriv_D (x : R) : x \in [set` I] `\ a -> is_derive x 1 D (dD x).
- move=> _.
  rewrite /D /dD.
  apply: is_derive_eq.
  by rewrite !fctE subr0 scaler1.
rewrite /taylor_remainder_peano.
rewrite (_ :
    (fun x : R => (f^`(d) x - T_(d; n.+1) x) / (x - a)^+n.+1) =
    (fun x : R => N x / D x)).
- apply: eq_fun.
  move=> x.
  by rewrite /N /D !fctE.
apply: lhopital.
- exact: a_in.
- rewrite [X in _ --> X](_ : 0 = N a).
  + change (0 = f^`(d) a - T_(d; n.+1) a).
    rewrite taylor_sum_center.
    by lra.
  apply: differentiable_continuous.
  apply/derivable1_diffP.
  apply: derivableB.
  + apply: fd_itv.
    exact: a_in.
  + exact: taylor_sum_derivable.
- rewrite [X in _ --> X](_ : 0 = D a).
  + by rewrite /D !fctE subrr expr0n.
  apply: differentiable_continuous.
  apply/derivable1_diffP.
  rewrite /D.
  by apply: ex_derive.
- move=> x.
  rewrite inE.
  move=> [_ xa].
  rewrite /dD.
  apply: mulf_neq0.
  + by rewrite pnatr_eq0.
  + apply: expf_neq0.
    apply/eqP.
    change (x <> a) in xa.
    by lra.
- rewrite (_ :
      (fun x : R => dN x / dD x) =
      (fun x : R => n.+1%:R^-1 * h_(d.+1; n) x)).
  + apply: eq_fun.
    move=> x.
    rewrite /dN /dD /taylor_remainder_peano.
    rewrite invfM.
    by ring.
  apply: cvgM0.
  + exact: cvg_cst.
  + exact: cvg_next.
Qed.

(* Repeated L'Hopital steps reduce the original remainder to h_(i; k-i). *)
Local Lemma cvg_taylor_remainder_peano_iter (i : nat) :
  (i < k)%N ->
  h_(i; k - i) x @[x --> a^'] --> 0 ->
  h_(0; k) x @[x --> a^'] --> 0.
Proof.
elim: i.
- move=> _.
  by rewrite subn0.
- move=> i IHi i_lt_k cvg_next.
  apply: IHi.
  + by lia.
  + rewrite (_ : (k - i)%N = (k - i.+1).+1).
    * by lia.
    apply: cvg_taylor_remainder_peano_step.
    * apply: F_Derivable_Near.
      by lia.
    * exact: cvg_next.
Qed.

Local Lemma cvg_taylor_remainder_peano : h_(0; k) x @[x --> a^'] --> 0.
Proof.
have remainder_cvg : h_(k.-1; k - k.-1) x @[x --> a^'] --> 0.
- rewrite (_ : (k - k.-1)%N = 1%N).
  + by lia.
  apply: cvg_taylor_remainder_peano1.
  exact: F_Derivable.
move: remainder_cvg.
apply: cvg_taylor_remainder_peano_iter.
by lia.
Qed.

Theorem taylor_theorem :
    (f x - taylor_sum f k a x) / (x - a)^+k @[x --> a] --> 0.
Proof.
change (h_(0; k) @ a --> 0).
rewrite -[X in _ --> X](taylor_remainder_peano_center 0 k).
apply/continuous_withinNx.
rewrite taylor_remainder_peano_center.
exact: cvg_taylor_remainder_peano.
Qed.

End taylor_theorem.
