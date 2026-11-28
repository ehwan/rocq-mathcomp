From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype derive realfun.
From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.

Require Import taylor_poly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section expansion.
Context (R : realType) (f : R -> R) (n : nat) (a : R).

Context (taylor_interval : interval R).
Context (a_in : a \in taylor_interval).

Context (F_Derivable : forall (k : nat), (k <= n)%N ->
  {in taylor_interval, forall (x' : R), derivable (derive1n k f) x' 1}).

Context (x : R) (x_in : x \in taylor_interval).

(* Taylor term as a function of the center. *)
Local Abbreviation taylor_center_term :=
  (fun k : nat => f^`(k) * cst k`!%:R^-1 * (cst x - id)^+k).

Local Lemma taylor_center_sumE (k : nat) (a' : R) :
  (\sum_(i < k.+1) taylor_center_term i) a' = taylor_sum f k a' x.
Proof.
rewrite /taylor_sum !fct_sumE.
apply: eq_bigr.
move=> i _.
by rewrite /taylor_term !fctE.
Qed.

Local Lemma taylor_center_term_derivable (k : nat) (a' : R) :
  (k <= n)%N -> a' \in taylor_interval -> derivable (taylor_center_term k) a' 1.
Proof.
move=> k_le_n center_in.
have df : is_derive a' 1 (f^`(k)) ('D_1 (f^`(k)) a').
- apply: derivableP.
  apply: F_Derivable.
  + exact: k_le_n.
  + exact: center_in.
by apply: ex_derive.
Qed.

Local Lemma derive_taylor_center_remainder (a' : R) :
  a' \in taylor_interval ->
  (cst (f x) - \sum_(i < n.+1) taylor_center_term i)^`() a' =
    (- f^`(n.+1) * cst n`!%:R^-1 * (cst x - id)^+n) a'.
Proof.
move=> center_in.
have terms_derivable (i : 'I_n.+1) : derivable (taylor_center_term i) a' 1.
- apply: taylor_center_term_derivable.
  + by rewrite -ltnS.
  + exact: center_in.
rewrite derive1E /=.
rewrite deriveB.
- exact: derivable_cst.
- apply: derivable_sum.
  exact: terms_derivable.
rewrite derive_cst sub0r.
rewrite !fctE.
apply: oppr_inj.
rewrite !mulNr !opprK.
rewrite derive_sum //=.
rewrite (_ :
    (\sum_(i < n.+1) 'D_1 (taylor_center_term i) a') =
      \sum_(i < n.+1)
        (f^`(i.+1) a' * i`!%:R^-1 * (x - a')^+i -
         f^`(i) a' * i`!%:R^-1 * i%:R * (x - a')^+i.-1)).
- apply: eq_bigr.
  move=> i _.
  have df : is_derive a' 1 (f^`(i)) ('D_1 (f^`(i)) a').
  + apply: derivableP.
    apply: F_Derivable.
    * by rewrite -ltnS.
    * exact: center_in.
  rewrite derive_val !fctE /GRing.scale /=.
  rewrite -derive1E -derive1nS.
  by ring.
elim: n.
- rewrite big_ord1 /=.
  rewrite !fact0 !expr0.
  by field.
- move=> m IH.
  rewrite big_ord_recr /=.
  rewrite IH.
  rewrite -derive1nS.
  rewrite factS natrM.
  by field.
Qed.

Lemma taylor_expansion_lagrange :
  exists2 xi : R, xi \in taylor_interval &
    f x = taylor_sum f n a x + f^`(n.+1) xi / (n.+1)`!%:R * (x - a)^+n.+1.
Proof.
case: (eqVneq x a) => [-> | x_neq_a].
- exists a.
  + exact: a_in.
  + rewrite taylor_sum_center.
    rewrite subrr expr0n /=.
    by lra.
- pose G := cst (f x) - \sum_(i < n.+1) taylor_center_term i.
  pose P := (cst x - id)^+n.+1.
  have G_derivable b : b \in taylor_interval -> derivable G b 1.
  + move=> b_in.
    apply: derivableB.
    * exact: derivable_cst.
    * apply: derivable_sum.
      move=> i.
      apply: taylor_center_term_derivable.
      -- by rewrite -ltnS.
      -- exact: b_in.
  have P_derivable b : derivable P b 1.
  + by apply: ex_derive.
  have dG b : b \in taylor_interval ->
      'D_1 G b = - f^`(n.+1) b * n`!%:R^-1 * (x - b)^+n.
  + move=> b_in.
    rewrite -derive1E.
    rewrite /G.
    rewrite derive_taylor_center_remainder //=.
    by rewrite !fctE.
  have dP b : 'D_1 P b = - (n.+1%:R * (x - b)^+n).
  + rewrite /P.
    rewrite derive_val !fctE /GRing.scale /=.
    by ring.
  have closed_subset : {subset `[minr a x, maxr a x]%R <= taylor_interval}.
  + case: taylor_interval a_in x_in => l u.
    rewrite !itv_boundlr.
    move=> /andP [la au] /andP [lx xu].
    apply: interval.subset_itv.
    * rewrite /minr.
      by case: ifP.
    * rewrite /maxr.
      by case: ifP.
  have min_lt_max : minr a x < maxr a x.
  + rewrite lt_max !gt_min !ltxx /= orbF.
    exact: lt_total.
  have sub_neq b : b \in `]minr a x, maxr a x[%R -> x - b != 0.
  + rewrite subr_eq0.
    move=> b_in.
    apply/eqP.
    move=> xb.
    move: b_in.
    rewrite -xb in_itv /=.
    by rewrite gt_min lt_max ltxx !orbF lt_asym.
  have succ_neq : n.+1%:R != 0 :> R.
  + by rewrite pnatr_eq0.
  have [xi xi_in ratio] :
      exists2 xi : R, xi \in `]minr a x, maxr a x[%R &
        'D_1 G xi / 'D_1 P xi =
          (G (maxr a x) - G (minr a x)) / (P (maxr a x) - P (minr a x)).
  + apply: cauchy_MVT.
    * exact: min_lt_max.
    * apply: derivable_within_continuous.
      move=> b b_in.
      apply: G_derivable.
      apply: closed_subset.
      exact: b_in.
    * apply: derivable_within_continuous.
      move=> b _.
      exact: P_derivable.
    * move=> b b_in.
      apply: derivableP.
      apply: G_derivable.
      apply: closed_subset.
      apply: subset_itv_oo_cc.
      exact: b_in.
    * move=> b _.
      apply: derivableP.
      exact: P_derivable.
    * move=> b b_in.
      rewrite dP oppr_eq0.
      apply: mulf_neq0.
      -- exact: succ_neq.
      -- apply: expf_neq0.
        apply: sub_neq.
        exact: b_in.
  have xi_in_interval : xi \in taylor_interval.
  + apply: closed_subset.
    apply: subset_itv_oo_cc.
    exact: xi_in.
  have derivative_ratio :
      'D_1 G xi / 'D_1 P xi = f^`(n.+1) xi / (n.+1)`!%:R.
  + rewrite dG //= dP.
    rewrite factS natrM.
    have fact_neq : n`!%:R != 0 :> R.
    * by rewrite pnatr_eq0 -lt0n fact_gt0.
    have xi_power_neq : (x - xi)^+n != 0.
    * apply: expf_neq0.
      apply: sub_neq.
      exact: xi_in.
    by field.
  have endpoint_ratio :
      (G (maxr a x) - G (minr a x)) / (P (maxr a x) - P (minr a x)) =
      (G a - G x) / (P a - P x).
  + rewrite /minr /maxr.
    case: ifP.
    * move=> _.
      rewrite -[G x - G a]opprB -[P x - P a]opprB.
      by rewrite divrNN.
    * by [].
  have power_neq : (x - a)^+n.+1 != 0.
  + apply: expf_neq0.
    by rewrite subr_eq0.
  exists xi.
  + exact: xi_in_interval.
  + rewrite -derivative_ratio ratio endpoint_ratio.
    rewrite /G /P !fctE.
    rewrite !taylor_center_sumE taylor_sum_center.
    rewrite !subrr expr0n /=.
    by field.
Qed.

Lemma taylor_expansion_bound (M : R) :
  {in taylor_interval, forall y : R, `|f^`(n.+1) y| <= M} ->
  `|f x - taylor_sum f n a x| <= M / n.+1`!%:R * `|x - a|^+n.+1.
Proof.
move=> bound.
move: taylor_expansion_lagrange => [xi xi_in expansion].
rewrite expansion addrAC subrr add0r.
rewrite normrM normf_div normrX normr_nat.
apply: ler_wpM2r.
- apply: exprn_ge0.
  exact: normr_ge0.
- apply: ler_wpM2r.
  + by rewrite invr_ge0 ler0n.
  + apply: bound.
    exact: xi_in.
Qed.

End expansion.
