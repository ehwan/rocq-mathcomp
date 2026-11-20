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
rewrite /taylor_sum.
rewrite !fct_sumE.
apply: eq_bigr => i _.
by rewrite /taylor_term !fctE.
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
rewrite derive1E //=.
rewrite deriveB.
- by apply: derivable_cst.
- apply: derivable_sum.
  move=> i.
  apply: taylor_center_term_derivable.
  move: (ltn_ord i).
  by lia.
exact: a_in.
rewrite derive_cst.
rewrite sub0r.
rewrite !fctE.
apply: oppr_inj.
rewrite !mulNr.
rewrite !opprK.
rewrite derive_sum.
- move=> i.
  apply: taylor_center_term_derivable.
  move: (ltn_ord i).
  by lia.
exact: a_in.
under eq_bigr.
  move=> i _.
  rewrite deriveM.
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

  rewrite deriveX.
  - apply: derivableB.
    + by apply: derivable_cst.
    + by apply: derivable_id.

  rewrite deriveB.
  - by apply: derivable_cst.
  - by apply: derivable_id.

  rewrite derive_cst.
  rewrite derive_id.

  rewrite deriveM.
  - apply: F_Derivable.
    move: (ltn_ord i).
    by lia.
    exact: a_in.
  - by apply: derivable_cst.
  rewrite derive_cst.

  rewrite -derive1E.
  rewrite -derive1nS.

  rewrite !/cst.
  rewrite !fctE /=.
  rewrite /GRing.scale /=.
  over.
simpl.

elim: n.
- rewrite big_ord1 //=.
  rewrite !fact0 !expr0.
  rewrite invr1.
  by ring.
- move=> m.
  move=> IH.
  rewrite big_ord_recr //=.
  rewrite IH.
  rewrite -derive1nS.
  rewrite factS.
  rewrite natrM.
  by field.
Qed.

Lemma taylor_remainder_lagrange :
  exists2 xi : R, xi \in taylor_interval &
    f x - taylor_sum f n a x = f^`(n.+1) xi / (n.+1)`!%:R * (x - a)^+n.+1.
Proof.
case: (eqVneq x a).
- move=> ->.
  exists a.
  + rewrite /minr /maxr ltxx.
    rewrite in_itv /=.
    by lra.
  + rewrite taylor_sum_center.
    rewrite !subrr expr0n /=.
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
  rewrite -derive1E.
  rewrite /G.
  rewrite remainder_derivate.
  + exact: b_in.
  + by rewrite !fctE.
have dP b : (b \in taylor_interval) -> 'D_1 P b = - (n.+1%:R * (x - b)^+n).
- move=> b_in.
  rewrite /P.
  rewrite deriveX.
  + exact: base_derivable.
  rewrite deriveB.
  + exact: derivable_cst.
  + exact: derivable_id.
  rewrite derive_cst derive_id.
  rewrite !fctE.
  rewrite /GRing.scale /=.
  by ring.
have min_lt_max : minr a x < maxr a x.
- rewrite /minr /maxr.
  case: ifP => // ax.
  by rewrite lt_neqAle x_neq_a leNgt ax.
have sub_neq b : b \in `]minr a x, maxr a x[%R -> x - b != 0.
- rewrite subr_eq0 => b_in.
  apply/eqP => xb.
  move: b_in.
  by rewrite -xb in_itv /= gt_min lt_max ltxx !orbF lt_asym.
have succ_neq : n.+1%:R != 0 :> R by rewrite pnatr_eq0.
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
    rewrite (dP b (subset_itv_oo_cc b_in)) oppr_eq0.
    exact: mulf_neq0 succ_neq (expf_neq0 n (sub_neq b b_in)).
have xi_in_closed : xi \in taylor_interval := subset_itv_oo_cc xi_in.
have derivative_ratio :
    'D_1 G xi / 'D_1 P xi = f^`(n.+1) xi / (n.+1)`!%:R.
- rewrite (dG xi xi_in_closed) (dP xi xi_in_closed) factS natrM.
  have fact_neq : n`!%:R != 0 :> R by rewrite pnatr_eq0 -lt0n fact_gt0.
  have xi_power_neq : (x - xi)^+n != 0 := expf_neq0 n (sub_neq xi xi_in).
  by field.
have endpoint_ratio :
    (G (maxr a x) - G (minr a x)) / (P (maxr a x) - P (minr a x)) =
    (G a - G x) / (P a - P x).
- rewrite /minr /maxr.
  case: ifP => // _.
  by rewrite -[G x - G a]opprB -[P x - P a]opprB divrNN.
have power_neq : (x - a)^+n.+1 != 0.
- apply: expf_neq0.
  by rewrite subr_eq0.
exists xi => //.
rewrite -derivative_ratio ratio endpoint_ratio /G /P.
rewrite !fctE !taylor_center_sumE taylor_sum_center !subrr expr0n /=.
by rewrite !subr0 divfK.
Qed.

Lemma taylor_expansion (M : R)
    (derivative_bound : {in taylor_interval, forall s : R, `|f^`(n.+1) s| <= M}) :
  `|f x - taylor_sum f n a x| <= M * `|x - a| ^+ n.+1.
Proof.
have [xi hxi ->] := taylor_remainder_lagrange.
rewrite normrM normf_div normrX.
apply: ler_wpM2r.
- exact: exprn_ge0 (normr_ge0 _).
have hf : 1 <= n.+1`!%:R :> R by rewrite ler1n fact_gt0.
rewrite normr_nat ler_pdivrMr ?ltr0n ?fact_gt0 //.
have bound := derivative_bound xi hxi.
have hM := le_trans (normr_ge0 _) bound.
by nra.
Qed.

End remainder.
