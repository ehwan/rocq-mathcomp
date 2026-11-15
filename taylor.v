From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau derive sequences realfun.

Require Import taylor_poly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Import Num.Def Num.Theory.

(* From Coq Require Import Reals. *)
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import zify.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section taylor_theorem.
Context (R : realType) (f : R -> R) (a : R).

(* f is k times differentiable. *)
Context (k: nat).
Context (k_gt0 : (0 < k)%N).
Context (F_Derivable : derivable (f^`(k.-1)) a 1).
Context (F_Derivable_Near: forall (d: nat), (d<k.-1)%N -> \forall x \near a, derivable f^`(d) x 1).
(* f^(k) (a) ->  f^(k-1) \near x *)
(* derivale f^(d) -> derivable f^(d-1) ? *)
(* Lemma F_Derivable_Near (d: nat): (d<k.-1)%N -> \forall x \near a, derivable f^`(d) x 1.
Proof.
elim: d.
- move=> dk.
  near=>x.
  (* Unset Printing Notations. *)
  Print derive1n.
  Print derive1.

  have kgt1: (1 < k)%N.
    admit.
  have FD2:= (@F_Derivable 1 kgt1).
  move: FD2.

  rw /derivable. *)
  (* exists f^`(1) (near a)  -->  derivable f^`(0) (near a) ? *)

  (* (derivable f^`(1) a 1) -> (derivable f^`(0) x 1).
  f^(1)' = lim h->0 ( f^(1) (near a) - f^(1)(x) ) / h, h!=0
  --> f^(1) (near a) が定義
  --> f^(0) が near aで微分可能 *)

  (* f` -> f_derivable  *)




  (* unfold derivable.
  apply/derivable1_diffP.
Check differentiable_def.
Search differentiable_def.
Admitted. *)

Local Notation "'T_' '(' d ';' n ')'" := (taylor_sum (f^`(d)) n a).

Local Lemma derive_iterated_taylor_sumS (d n : nat) (x : R) :
  'D_1 T_(d; n.+1) x = T_(d.+1; n) x.
Proof. by rw derive_taylor_sumS -derive1nS. Qed.

Local Lemma cvg_taylor_sum (d n: nat) : T_(d; n) @ a --> f^`(d) a.
Proof.
rw -(taylor_sum_center (f^`(d)) a n).
apply: differentiable_continuous.
apply/derivable1_diffP.
exact: taylor_sum_derivable.
Qed.

Local Definition taylor_remainder_peano (d n : nat) (x: R) :=
  (f^`(d) x - T_(d;n) x) / (x - a)^+n.
Local Notation "'h_' '(' d ';' n ')'" := (taylor_remainder_peano d n).

Local Lemma taylor_remainder_peano_center (d n: nat) : h_(d; n) a = 0.
Proof.
rw /taylor_remainder_peano.
rw taylor_sum_center.
by lra.
Qed.

Local Lemma cvg_iterated_derive_increment (d : nat) :
  derivable (f^`(d)) a 1 ->
  (f^`(d) (a + h) - f^`(d) a) / h @[h --> (0 : R)^'] --> f^`(d.+1) a.
Proof.
move=> df.
rw derive1nS derive1E.
rw (_ : (fun h : R => (f^`(d) (a + h) - f^`(d) a) / h) =
  (fun h : R => h^-1 *: ((f^`(d) \o shift a) (h *: 1) - f^`(d) a))).
- apply/funext => h.
  rw /comp /shift.
  rw scaler1.
  rw [h + a]addrC.
  rw /GRing.scale /=.
  by rw mulrC.
exact: df.
Qed.

Local Lemma cvg_iterated_derive (d : nat) :
  derivable (f^`(d)) a 1 ->
  (f^`(d) x - f^`(d) a) / (x - a) @[x --> a^'] --> f^`(d.+1) a.
Proof.
move=> df.
rw (_ : (fun x : R => (f^`(d) x - f^`(d) a) / (x - a)) =
  (fun h => (f^`(d) (a + h) - f^`(d) a) / h) \o (fun x => x - a)).
- apply: eq_fun => x.
  rw /comp.
  by rw subrKC.
have shift_cvgr : x - a @[x --> a^'] --> (0 : R)^'.
- rw /dnbhs.
  apply/cvg_to_withinP.
  split.
  + rw -(subrr a).
    apply: cvgB.
    * exact: nbhs_dnbhs.
    * exact: cvg_cst.
  + apply: (filterS (P := fun x : R => x != a)).
    * move=> x /=.
      rw subr_eq0.
      exact: id.
    * exact: nbhs_dnbhs_neq a.
apply: cvg_comp.
- exact: shift_cvgr.
- apply: cvg_iterated_derive_increment.
  exact: df.
Qed.

(* A first-order remainder follows directly from differentiability. *)
Local Lemma cvg_taylor_remainder_peano1 (d: nat) :
  derivable (f^`(d)) a 1 -> h_(d; 1) x @[x --> a^'] --> 0.
Proof.
move=> df.
apply: (@cvg_trans _
  ((fun x : R => (f^`(d) x - f^`(d) a) / (x - a)
                  - f^`(d.+1) a) @ a^')).
- change ((h_(d; 1) @ a^') -->
    ((fun x : R => (f^`(d) x - f^`(d) a) / (x - a)
                    - f^`(d.+1) a) @ a^')).
  apply: (near_eq_cvg
    (f := fun x : R => (f^`(d) x - f^`(d) a) / (x - a) - f^`(d.+1) a)).
  apply: (filterS (P := fun x : R => x - a != 0)).
  + change (forall x : R, x - a != 0 ->
      (f^`(d) x - f^`(d) a) / (x - a) - f^`(d.+1) a = h_(d; 1) x).
    move=> x xa.
    rw /taylor_remainder_peano.
    rw taylor_sumS taylor_sum0.
    rw /taylor_term !fctE.
    rw derive1n1 -derive1nS.
    rw factS fact0 /=.
    rw !expr1.
    by field.
  + change (\forall x \near a^', x - a != 0).
    apply: filterS (nbhs_dnbhs_neq a).
    by move=> x; rw subr_eq0.
- change ((fun x : R =>
    (f^`(d) x - f^`(d) a) / (x - a) - f^`(d.+1) a) @ a^' --> (0 : R)).
  rw -(subrr (f^`(d.+1) a)).
  apply: cvgB.
  + apply: cvg_iterated_derive.
    exact: df.
  + exact: cvg_cst.
Qed.

(* One L'Hopital step moves one derivative into the Taylor degree. *)
Local Lemma cvg_taylor_remainder_peano_step (d n: nat) :
  (\forall x \near a, derivable (f^`(d)) x 1) ->
  h_(d.+1; n) x @[x --> a^'] --> 0 ->
  h_(d; n.+1) x @[x --> a^'] --> 0.
Proof.
move=> fd cvg_next.
move/nbhs_normP: (fd) => [r r_gt0 fd_ball].
change (is_true (0 < r)) in r_gt0.
have fd_itv (x: R) : x \in `]a - r, a + r[%R ->
    derivable (f^`(d)) x 1.
- move=> x_in_range.
  apply: fd_ball.
  rw /ball_ /=.
  rw ltr_distlC.
  move: x_in_range.
  by rw in_itv /=.
rw /taylor_remainder_peano.
apply: (lhopital (a := a - r) (b := a + r)
  (df := fun x => f^`(d.+1) x - T_(d.+1; n) x)
  (dg := fun x => n.+1%:R * (x - a)^+n)).
- rw in_itv /=.
  by lra.
- move=> x.
  rw inE.
  move=> [xr xa].
  apply: DeriveDef.
  + apply: derivableB.
    * apply: fd_itv.
      by rw inE.
    * exact: taylor_sum_derivable.
  + rw deriveB.
    * apply: fd_itv.
      by rw inE.
    * exact: taylor_sum_derivable.
    * rw -derive1E -derive1nS.
      by rw derive_iterated_taylor_sumS.
- move=> x _.
  rw -(_: ((id - cst a)^+n.+1 : R -> R) =
    (fun x => (x - a)^+n.+1)).
  + apply/funext => y.
    by rw !fctE.
  apply: DeriveDef.
  + apply: derivableX.
    apply: derivableB.
    * exact: derivable_id.
    * exact: derivable_cst.
  + rw deriveX.
    * apply: derivableB.
      -- exact: derivable_id.
      -- exact: derivable_cst.
    * rw deriveB ?derivable_id ?derivable_cst //.
      rw derive_id derive_cst.
      rw subr0 scaler1.
      by rw !fctE.
- rw -(subrr (f^`(d) a)).
  apply: cvgB.
  + apply: differentiable_continuous.
    apply/derivable1_diffP.
    move: fd.
    exact: nbhs_singleton.

  + exact: cvg_taylor_sum.
- rw -[X in _ --> X](@expr0n R n.+1).
  change (((fun y : R => y^+n.+1) \o (fun x : R => x - a)) @ a -->
    (0 : R)^+n.+1).
  apply: continuous_cvg.
  + exact: exprn_continuous.
  + rw -[X in _ --> X](subrr a).
    apply: cvgB.
    * exact: cvg_id.
    * exact: cvg_cst.
- move=> x.
  rw inE.
  move=> [_ xa].
  rw mulf_neq0 ?pnatr_eq0 //.
  apply: expf_neq0.
  change (x <> a) in xa.
  by lra.
- rw (_:
      (fun x => (f^`(d.+1) x - T_(d.+1; n) x) /
        (n.+1%:R * (x - a)^+n)) =
      (fun x => n.+1%:R^-1 * h_(d.+1; n) x)).
  + apply/funext => x.
    rw /taylor_remainder_peano.
    rw invfM.
    by ring.
  rw -(mulr0 n.+1%:R^-1).
  apply: cvgMl_tmp.
  exact: cvg_next.
Qed.

(* Repeated L'Hopital steps reduce the original remainder to h_(i; k-i). *)
Local Lemma cvg_taylor_remainder_peano_iter (i: nat) :
  (i < k)%N ->
  h_(i; k - i) x @[x --> a^'] --> 0 ->
  h_(0; k) x @[x --> a^'] --> 0.
Proof.
elim: i.
- move=> _.
  by rw subn0.
- move=> i IHi i_lt_k cvg_next.
  apply: IHi.
  + by lia.
  + rw -(subnSK (ltnW i_lt_k)).
    apply: cvg_taylor_remainder_peano_step.
    * apply: F_Derivable_Near.
      by lia.
    * exact: cvg_next.
Qed.

Local Lemma cvg_taylor_remainder_peano : h_(0; k) x @[x --> a^'] --> 0.
Proof.
apply: (cvg_taylor_remainder_peano_iter (i := k.-1)).
- by lia.
- rw (_ : (k - k.-1)%N = 1%N).
  + by lia.
  apply: cvg_taylor_remainder_peano1.
  apply: F_Derivable.
Qed.

Theorem taylor_theorem :
    (f x - taylor_sum f k a x) / (x - a)^+k @[x --> a] --> 0.
Proof.
rw -(taylor_remainder_peano_center 0 k).
apply/(continuous_withinNx _ _).2.
rw taylor_remainder_peano_center.
exact: cvg_taylor_remainder_peano.
Qed.

End taylor_theorem.
