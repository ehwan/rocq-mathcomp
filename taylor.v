From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau derive sequences realfun.

Require Import sequence.

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

Section taylor_theorem.
Context (R : realType) (f : R -> R) (k : nat) (a r : R).
Context (r_gt0 : 0 < r).
Context (F_Derivable : forall d (x : R), (d <= k)%N ->
  x \in `]a - r, a + r[%R -> derivable (f^`(d)) x 1).

(* T_{d;n}: the degree-n Taylor polynomial of the dth derivative of f.
   The sum includes i = 0, ..., n, hence n + 1 terms. *)
Definition taylor_term (d n : nat) : R -> R :=
  cst (f^`(d + n) a) * cst n`!%:R^-1 * (id - cst a)^+n.

Definition taylor_sum (d n : nat) :=
  \sum_(i < n.+1) taylor_term d i.

Definition taylor_quotient (d n : nat) x :=
  (f^`(d) x - taylor_sum d n x) / (x - a)^+n.

Local Notation "'T_' '(' d ';' n ')'" := (taylor_sum d n).
Local Notation "'h_' '(' d ';' n ')'" := (taylor_quotient d n).

Lemma taylor_term_derivable d n x : derivable (taylor_term d n) x 1.
Proof.
apply: derivableM.
- apply: derivableM.
  + exact: derivable_cst.
  + exact: derivable_cst.
- apply: derivableX.
  apply: derivableB.
  + exact: derivable_id.
  + exact: derivable_cst.
Qed.

Lemma taylor_sum_derivable d n x : derivable T_(d; n) x 1.
Proof.
apply: derivable_sum.
move=> i.
exact: taylor_term_derivable.
Qed.

Lemma taylor_sum0 d x : T_(d; 0) x = f^`(d) a.
Proof.
rewrite /taylor_sum big_ord1.
rewrite /taylor_term !fctE.
rewrite addn0 fact0 expr0.
by rewrite invr1 !mulr1.
Qed.

Lemma taylor_term_centerS d n : taylor_term d n.+1 a = 0.
Proof.
rewrite /taylor_term !fctE.
rewrite subrr expr0n.
by rewrite mulr0.
Qed.

Lemma taylor_sumS d n x :
  T_(d; n.+1) x = T_(d; n) x + taylor_term d n.+1 x.
Proof.
by rewrite /taylor_sum big_ord_recr /= fctE.
Qed.

Lemma taylor_sum_center d n : T_(d; n) a = f^`(d) a.
Proof.
elim: n.
- exact: taylor_sum0.
- move=> n IHn.
  rewrite taylor_sumS.
  rewrite IHn taylor_term_centerS.
  by rewrite addr0.
Qed.


Lemma derive_taylor_term0 d x : 'D_1 (taylor_term d 0) x = 0.
Proof.
have -> : taylor_term d 0 = cst (f^`(d) a).
- apply/funext => y.
  rewrite /taylor_term !fctE.
  rewrite addn0 fact0 expr0.
  by rewrite invr1 !mulr1.
exact: derive_cst.
Qed.

Lemma derive_taylor_termS d n x :
  'D_1 (taylor_term d n.+1) x = taylor_term d.+1 n x.
Proof.
have dxa : derivable (id - cst a) x 1.
- apply: derivableB.
  + exact: derivable_id.
  + exact: derivable_cst.
have dc : derivable
    (cst (f^`(d + n.+1) a) * cst (n.+1)`!%:R^-1) x 1.
- apply: derivableM.
  + exact: derivable_cst.
  + exact: derivable_cst.
have dx : derivable ((id - cst a)^+n.+1) x 1.
- apply: derivableX.
  exact: dxa.
rewrite /taylor_term (deriveM dc dx).
clear dc dx.
rewrite deriveX //.
rewrite deriveB ?derivable_id ?derivable_cst //.
rewrite derive_id derive_cst.
rewrite subr0 scaler1.
rewrite deriveM ?derivable_cst // !derive_cst.
rewrite !scaler0 add0r scaler0 addr0.
rewrite !fctE.
rewrite addnS addSn /=.
rewrite /GRing.scale /=.
have factS_E : (n.+1)`!%:R = n.+1%:R * n`!%:R :> R.
- by rewrite factS natrM.
have fact_neq0 : n`!%:R != 0 :> R.
- by rewrite pnatr_eq0 -lt0n fact_gt0.
have factS_neq0 : (n.+1)`!%:R != 0 :> R.
- by rewrite pnatr_eq0 -lt0n fact_gt0.
by field: factS_E.
Qed.

Lemma derive_taylor_sumS d n x :
  'D_1 T_(d; n.+1) x = T_(d.+1; n) x.
Proof.
rewrite /taylor_sum derive_sum.
- move=> i.
  exact: taylor_term_derivable.
- rewrite big_ord_recl /= derive_taylor_term0 add0r fct_sumE.
  apply: eq_bigr => i _.
  by rewrite derive_taylor_termS.
Qed.

Lemma cvg_taylor_sum d n : T_(d; n) @ a --> f^`(d) a.
Proof.
have ct : T_(d; n) @ a --> T_(d; n) a.
- exact/differentiable_continuous/derivable1_diffP/taylor_sum_derivable.
by move: ct; rewrite taylor_sum_center.
Qed.

Lemma taylor_quotient0 d x : h_(d; 0) x = f^`(d) x - f^`(d) a.
Proof.
rewrite /taylor_quotient taylor_sum0.
by rewrite expr0 divr1.
Qed.

Lemma taylor_quotient_center d n : h_(d; n) a = 0.
Proof.
rewrite /taylor_quotient taylor_sum_center.
by rewrite subrr mul0r.
Qed.

Lemma taylor_center_in_range : a \in `]a - r, a + r[%R.
Proof.
rewrite in_itv /=.
have rp := r_gt0.
apply/andP.
split.
- by lra.
- by lra.
Qed.

(* Induct on n with d + n <= k. L'Hopital transfers the limit of
   h_{d;n+1} to that of h_{d+1;n} / (n+1). *)
Lemma cvg_taylor_quotient d n : (d + n <= k)%N ->
  h_(d; n) x @[x --> a^'] --> 0.
Proof.
elim: n d.
- move=> d dk.
  have cd : {for a, continuous (f^`(d))}.
  + apply/differentiable_continuous/derivable1_diffP.
    apply: F_Derivable.
    * by move: dk; rewrite addn0.
    * exact: taylor_center_in_range.
  have -> : h_(d; 0) = (fun x => f^`(d) x - f^`(d) a).
  + apply/funext => x.
    exact: taylor_quotient0.
  rewrite -[X in _ --> X](subrr (f^`(d) a)).
  apply: cvgB.
  + exact: cvg_within_filter cd.
  + exact: cvg_cst.
- move=> n IHn d dnk.
  have dk : (d < k)%N.
  + apply: leq_trans _ dnk.
    by rewrite addnS ltnS leq_addr.
  have cd : {for a, continuous (f^`(d))}.
  + apply/differentiable_continuous/derivable1_diffP.
    apply: F_Derivable.
    * exact: ltnW dk.
    * exact: taylor_center_in_range.
  have cnum : (f^`(d) x - T_(d; n.+1) x) @[x --> a] --> 0.
  + rewrite -[X in _ --> X](subrr (f^`(d) a)).
    apply: cvgB.
    * exact: cd.
    * exact: cvg_taylor_sum.
  have cden : (x - a)^+n.+1 @[x --> a] --> (0 : R).
  + rewrite -[X in _ --> X](@expr0n R n.+1).
    apply: (@continuous_cvg _ _ _ _ _ (fun x : R => x - a)
      (fun y : R => y^+n.+1) 0).
    * exact: exprn_continuous.
    * rewrite -[X in _ --> X](subrr a).
      apply: cvgB.
      -- exact: cvg_id.
      -- exact: cvg_cst.
  have dnum (x : R) : x \in `]a - r, a + r[ `\ a ->
      is_derive x 1 (f^`(d) - T_(d; n.+1))
        (f^`(d.+1) x - T_(d.+1; n) x).
  + rewrite inE.
    move=> [xr xa].
    apply: DeriveDef.
    * apply: derivableB.
      -- apply: F_Derivable (ltnW dk) _.
         by rewrite inE.
      -- exact: taylor_sum_derivable.
    * rewrite deriveB.
      -- apply: F_Derivable (ltnW dk) _.
         by rewrite inE.
      -- exact: taylor_sum_derivable.
      -- rewrite -derive1E -derive1nS.
         by rewrite derive_taylor_sumS.
  have powerE : ((id - cst a)^+n.+1 : R -> R) =
      (fun x => (x - a)^+n.+1).
  + apply/funext => x.
    by rewrite !fctE.
  have dden (x : R) : is_derive x 1 (fun x => (x - a)^+n.+1)
      (n.+1%:R * (x - a)^+n).
  + rewrite -powerE.
    apply: DeriveDef.
    * apply: derivableX.
      apply: derivableB.
      -- exact: derivable_id.
      -- exact: derivable_cst.
    * rewrite deriveX.
      -- apply: derivableB.
         ++ exact: derivable_id.
         ++ exact: derivable_cst.
      -- rewrite deriveB ?derivable_id ?derivable_cst //.
         rewrite derive_id derive_cst.
         rewrite subr0 scaler1.
         by rewrite !fctE.
  have den_neq0 (x : R) : x \in `]a - r, a + r[ `\ a ->
      n.+1%:R * (x - a)^+n != 0.
  + rewrite inE.
    move=> [_ xa].
    rewrite mulf_neq0 ?pnatr_eq0 //.
    apply: expf_neq0.
    rewrite subr_eq0.
    apply/eqP => xeq.
    apply: xa.
    by symmetry.
  (* Its value at a is zero, so the induction hypothesis also gives
     the unpunctured limit required by the library's L'Hopital lemma. *)
  have q0 := taylor_quotient_center d.+1 n.
  have ihfull : h_(d.+1; n) @ a --> 0.
  + rewrite -q0.
    apply/(continuous_withinNx _ _).2.
    rewrite q0.
    apply: IHn.
    by rewrite addSn -addnS.
  rewrite /taylor_quotient.
  apply: (@lhopital R
    (fun x => f^`(d) x - T_(d; n.+1) x)
    (fun x => f^`(d.+1) x - T_(d.+1; n) x)
    (fun x => (x - a)^+n.+1) (fun x => n.+1%:R * (x - a)^+n)
    (a - r) (a + r) a 0).
  + exact: taylor_center_in_range.
  + exact: cnum.
  + exact: cden.
  + exact: den_neq0.
  + have -> :
        (fun x => (f^`(d.+1) x - T_(d.+1; n) x) /
          (n.+1%:R * (x - a)^+n)) =
        (fun x => n.+1%:R^-1 * h_(d.+1; n) x).
    * apply/funext => x.
      rewrite /taylor_quotient invfM.
      by ring.
    rewrite -(mulr0 n.+1%:R^-1).
    exact: cvgMl_tmp ihfull.
Qed.

Theorem taylor_theorem :
  exists h : R -> R,
    (forall x : R, h x * (x - a)^+k =
      f x - T_(0; k) x) /\
    h x @[x --> a] --> 0.
Proof.
exists h_(0; k).
split.
- move=> x.
  case: (eqVneq x a).
  + move=> ->.
    rewrite taylor_quotient_center taylor_sum_center.
    rewrite derive1n0.
    by rewrite mul0r subrr.
  + move=> xa.
    have pow_neq0 : (x - a)^+k != 0.
    * apply: expf_neq0.
      by rewrite subr_eq0.
    rewrite /taylor_quotient derive1n0.
    by field.
- have q0 := taylor_quotient_center 0 k.
  rewrite -q0.
  apply/(continuous_withinNx _ _).2.
  rewrite q0.
  apply: (cvg_taylor_quotient (d:=0)).
  by rewrite add0n.
Qed.

End taylor_theorem.
