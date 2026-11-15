From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau derive sequences
  realfun.

Require Import taylor_poly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Import Num.Def Num.Theory.

From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import zify.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section remainder.
Context (R : realType) (f : R -> R) (n : nat) (a x : R).

Local Abbreviation taylor_interval := (`[minr a x, maxr a x]%R).

Context (F_Derivable : forall (k : nat), (k <= n)%N ->
  {in taylor_interval, forall x', derivable (derive1n k f) x' 1}
  ).

(* Taylor term as a function of the center. *)
Local Abbreviation taylor_center_term :=
  (fun k : nat => f^`(k) * cst k`!%:R^-1 * (cst x - id)^+k).

Local Lemma taylor_center_sumE (k : nat) (a' : R) :
  (\sum_(i < k.+1) taylor_center_term i) a' = taylor_sum f k a' x.
Proof.
rw /taylor_sum.
rw !fct_sumE.
apply: eq_bigr => i _.
by rw /taylor_term !fctE.
Qed.

Local Lemma taylor_center_term_derivable (k : nat) (a' : R) :
  (k <= n)%N -> a' \in taylor_interval -> derivable (taylor_center_term k) a' 1.
Proof.
move=> k_le_n a_in.
apply: derivableM.
- apply: derivableM.
  + apply: F_Derivable.
    exact: k_le_n.
    exact: a_in.
  + by apply: derivable_cst.
- apply: derivableX.
  apply: derivableB.
  + by apply: derivable_cst.
  + by apply: derivable_id.
Qed.

Local Lemma remainder_derivate (a': R) :
  a' \in taylor_interval ->
  (cst (f x) - \sum_(i < n.+1) taylor_center_term i)^`() a' =
    (- f^`(n.+1) * cst n`!%:R^-1 * (cst x - id)^+n) a'.
Proof.
move=> a_in.
rw derive1E //=.
rw deriveB.
- by apply: derivable_cst.
- apply: derivable_sum.
  move=> i.
  apply: taylor_center_term_derivable.
  move: (ltn_ord i).
  by lia.
exact: a_in.
rw derive_cst.
rw sub0r.
rw !fctE.
apply: oppr_inj.
rw !mulNr.
rw !opprK.
rw derive_sum.
- move=> i.
  apply: taylor_center_term_derivable.
  move: (ltn_ord i).
  by lia.
exact: a_in.
under eq_bigr.
  move=> i _.
  rw deriveM.
  - apply: derivableM.
    + apply: F_Derivable.
      move: (ltn_ord i).
      by lia.
      exact: a_in.
    + by apply: derivable_cst.
  - apply: derivableX.
    apply: derivableB.
    + by apply: derivable_cst.
    + by apply: derivable_id.

  rw deriveX.
  - apply: derivableB.
    + by apply: derivable_cst.
    + by apply: derivable_id.

  rw deriveB.
  - by apply: derivable_cst.
  - by apply: derivable_id.

  rw derive_cst.
  rw derive_id.

  rw deriveM.
  - apply: F_Derivable.
    move: (ltn_ord i).
    by lia.
    exact: a_in.
  - by apply: derivable_cst.
  rw derive_cst.

  rw -derive1E.
  rw -derive1nS.

  rw !/cst.
  rw !fctE /=.
  rw /GRing.scale /=.
  over.
simpl.

elim: n.
- rw big_ord1 //=.
  rw !fact0 !expr0.
  rw invr1.
  by ring.
- move=> m.
  move=> IH.
  rw big_ord_recr //=.
  rw IH.
  rw -derive1nS.
  rw factS.
  rw natrM.
  by field.
Qed.

Lemma taylor_remainder_lagrange :
  exists2 xi : R, xi \in taylor_interval &
    f x - taylor_sum f n a x = f^`(n.+1) xi / (n.+1)`!%:R * (x - a)^+n.+1.
Proof.
case: (eqVneq x a).
- move=> ->.
  exists a.
  + rw /minr /maxr ltxx.
    rw in_itv /=.
    by lra.
  + rw taylor_sum_center.
    rw !subrr expr0n /=.
    by lra.
move=> x_neq_a.
(* wlog: /(x<a).

wlog:a /(x < a).
without loss of ge *)
pose G := cst (f x) - \sum_(i < n.+1) taylor_center_term i.
pose P := (cst x - id)^+n.+1.
have base_derivable b : derivable (cst x - id) b 1.
- apply: derivableB.
  + exact: derivable_cst.
  + exact: derivable_id.
have G_derivable b : b \in taylor_interval -> derivable G b 1.
- move=> b_in.
  apply: derivableB.
  + exact: derivable_cst.
  apply: derivable_sum => i.
  apply: taylor_center_term_derivable.
  + move: (ltn_ord i).
    by lia.
  + exact: b_in.
have P_derivable b : derivable P b 1.
- apply: derivableX.
  exact: base_derivable.
have dG b : (b \in taylor_interval) -> 'D_1 G b = - f^`(n.+1) b * n`!%:R^-1 * (x - b)^+n.
- move=> b_in.
  rw -derive1E.
  rw /G.
  rw remainder_derivate.
  + exact: b_in.
  + by rw !fctE.
have dP b : (b \in taylor_interval) -> 'D_1 P b = - (n.+1%:R * (x - b)^+n).
- move=> b_in.
  rw /P.
  rw deriveX.
  + exact: base_derivable.
  rw deriveB.
  + exact: derivable_cst.
  + exact: derivable_id.
  rw derive_cst derive_id.
  rw !fctE.
  rw /GRing.scale /=.
  by ring.
have min_lt_max : minr a x < maxr a x.
- rw /minr /maxr.
  case: ifP => // ax.
  by rw lt_neqAle x_neq_a leNgt ax.
have sub_neq b : b \in `]minr a x, maxr a x[%R -> x - b != 0.
- rw subr_eq0 => b_in.
  apply/eqP => xb.
  move: b_in.
  by rw -xb in_itv /= gt_min lt_max ltxx !orbF lt_asym.
have succ_neq : n.+1%:R != 0 :> R by rw pnatr_eq0.
have [xi xi_in ratio] :
    exists2 xi : R, xi \in `]minr a x, maxr a x[%R &
      'D_1 G xi / 'D_1 P xi =
        (G (maxr a x) - G (minr a x)) / (P (maxr a x) - P (minr a x)).
- apply: cauchy_MVT.
  + exact: min_lt_max.
  + exact: derivable_within_continuous G_derivable.
  + by apply: derivable_within_continuous => b _; exact: P_derivable.
  + move=> b b_in.
    apply: derivableP.
    apply: G_derivable.
    apply: subset_itv_oo_cc.
    exact: b_in.
  + by move=> b _; apply: derivableP; exact: P_derivable.
  + move=> b b_in.
    rw (dP b (subset_itv_oo_cc b_in)) oppr_eq0.
    exact: mulf_neq0 succ_neq (expf_neq0 n (sub_neq b b_in)).
have xi_in_closed : xi \in taylor_interval := subset_itv_oo_cc xi_in.
have derivative_ratio :
    'D_1 G xi / 'D_1 P xi = f^`(n.+1) xi / (n.+1)`!%:R.
- rw (dG xi xi_in_closed) (dP xi xi_in_closed) factS natrM.
  have fact_neq : n`!%:R != 0 :> R by rw pnatr_eq0 -lt0n fact_gt0.
  have xi_power_neq : (x - xi)^+n != 0 := expf_neq0 n (sub_neq xi xi_in).
  by field.
have endpoint_ratio :
    (G (maxr a x) - G (minr a x)) / (P (maxr a x) - P (minr a x)) =
    (G a - G x) / (P a - P x).
- rw /minr /maxr.
  case: ifP => // _.
  by rw -[G x - G a]opprB -[P x - P a]opprB divrNN.
have power_neq : (x - a)^+n.+1 != 0.
- apply: expf_neq0.
  by rw subr_eq0.
exists xi => //.
rw -derivative_ratio ratio endpoint_ratio /G /P.
rw !fctE !taylor_center_sumE taylor_sum_center !subrr expr0n /=.
by rw !subr0 divfK.
Qed.

End remainder.
