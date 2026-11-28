From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype derive.
From mathcomp Require Import ring_tactic field_tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition taylor_term (R : realType) (f : R -> R) (i : nat) (a : R) : R -> R :=
  cst (f^`(i) a) * cst i`!%:R^-1 * (id - cst a)^+i.

Definition taylor_sum (R : realType) (f : R -> R) (n : nat) (a : R) : R -> R :=
  \sum_(i < n.+1) taylor_term f i a.

Section taylor_polynomial.
Context (R : realType) (f : R -> R) (a : R).

Local Notation "'t_' '(' n ')'" := (taylor_term f n a).
Local Notation "'T_' '(' n ')'" := (taylor_sum f n a).

Lemma taylor_term_derivable (n : nat) (x : R) : derivable t_(n) x 1.
Proof.
rewrite /taylor_term.
by apply: ex_derive.
Qed.

Lemma taylor_sum_derivable (n : nat) (x : R) : derivable T_(n) x 1.
Proof.
apply: derivable_sum.
move=> i.
exact: taylor_term_derivable.
Qed.

Lemma taylor_term0 (x : R) : t_(0) x = f a.
Proof.
rewrite /taylor_term !fctE.
rewrite derive1n0.
rewrite fact0 expr0.
by field.
Qed.

Lemma taylor_sum0 (x : R) : T_(0) x = f a.
Proof.
rewrite /taylor_sum big_ord1.
exact: taylor_term0.
Qed.

Lemma taylor_term_centerS (n : nat) : t_(n.+1) a = 0.
Proof.
rewrite /taylor_term !fctE.
rewrite subrr expr0n /=.
by ring.
Qed.

Lemma taylor_sumS (n : nat) (x : R) :
  T_(n.+1) x = T_(n) x + t_(n.+1) x.
Proof.
by rewrite /taylor_sum big_ord_recr.
Qed.

Lemma taylor_sum_center (n : nat) : T_(n) a = f a.
Proof.
elim: n.
- exact: taylor_sum0.
- move=> n IH.
  rewrite taylor_sumS.
  rewrite IH.
  rewrite taylor_term_centerS.
  by ring.
Qed.

Lemma taylor_linear (delta : R) :
  taylor_sum f 1 a (a + delta) = f a + f^`(1) a * delta.
Proof.
rewrite taylor_sumS taylor_sum0.
rewrite /taylor_term !fctE.
rewrite expr1 (_ : 1`! = 1%N) //.
by field.
Qed.

Lemma taylor_quadratic (delta : R) :
  taylor_sum f 2 a (a + delta) =
    f a + f^`(1) a * delta + f^`(2) a * delta ^+ 2 / 2.
Proof.
rewrite taylor_sumS taylor_linear.
rewrite /taylor_term !fctE.
rewrite (_ : 2`! = 2%N) //.
by field.
Qed.

Lemma derive_taylor_term0 (x : R) : 'D_1 t_(0) x = 0.
Proof.
rewrite (_ : t_(0) = cst (f a)).
- apply: eq_fun.
  move=> x'.
  exact: taylor_term0.
exact: derive_cst.
Qed.

Lemma derive_taylor_termS (n : nat) (x : R) :
  'D_1 t_(n.+1) x = taylor_term (f^`()) n a x.
Proof.
rewrite /taylor_term.
rewrite derive_val !fctE.
rewrite derive1Sn.
rewrite factS natrM.
rewrite /GRing.scale /=.
by field.
Qed.

Lemma derive_taylor_sum0 (x : R) : 'D_1 T_(0) x = 0.
Proof.
rewrite /taylor_sum big_ord1.
exact: derive_taylor_term0.
Qed.

Lemma derive_taylor_sumS (n : nat) (x : R) :
  'D_1 T_(n.+1) x = taylor_sum (f^`()) n a x.
Proof.
rewrite /taylor_sum.
rewrite derive_sum.
- move=> i.
  exact: taylor_term_derivable.
rewrite big_ord_recl /=.
rewrite derive_taylor_term0 add0r.
rewrite fct_sumE.
apply: eq_bigr.
move=> i _.
by rewrite derive_taylor_termS.
Qed.

End taylor_polynomial.
