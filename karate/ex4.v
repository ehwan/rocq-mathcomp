From mathcomp Require Import all_ssreflect.
From mathcomp Require Import boolp.

Search "propositional".

Lemma Ex411:
    True = true.
Proof.
    apply: propositional_extensionality.
    split.
    - by [].
    - by [].
Qed.

Check setI.

From mathcomp Require Import classical_sets.

(* Open Scope classical_set_scope. *)
Definition A : set nat := [ set n | n = 1 \/ n = 2].

Search "morgan".

(* De Morgan's law 1 *)
Lemma Ex421_1 (T: Type) (s1 s2 : set T) :
    setC (setU s1 s2) = setI (setC s1) (setC s2).
    Search "seteq".
    rewrite /setC /setI /setU.
    apply/seteqP.
    split.
    - move=> x.
      move=> h1.
      change (~ (s1 x \/ s2 x)) in h1.
      split.
      - move=> h2.
        apply: h1.
        by left.
      - move=> h2.
        apply: h1.
        by right.
    - move=> x.
      cbn.
      move=> [h11 h12].
      move=> [h21 | h22].
      - apply: h11.
        by apply: h21.
      - apply: h12.
        by apply: h22.
Qed.

(* De Morgan's law 2 *)
Lemma Ex421_2 (T: Type) (s1 s2 : set T) :
    setC (setI s1 s2) = setU (setC s1) (setC s2).
    Search "seteq".
    rewrite /setC /setI /setU.
    apply/seteqP.
    split.
    - move=> x.
      cbn.
      move=> h1.
      case: (pselect (s1 x)).
      - right.
        move => hs2.
        apply: h1.
        split.
        - exact: a.
        - exact: hs2.
      - left.
        exact: b.
    - move=> x.
      cbn.
      move=> [h11 | h12].
      - move=> [hx hy].
        by apply: h11 hx.
      - move=> [hx hy].
        by apply: h12 hy.
Qed.

(* De Morgan's law 2 with pure Rocq *)
Lemma Ex421_3 (T: Type) (s1 s2 : set T) :
    setC (setI s1 s2) = setU (setC s1) (setC s2).
Proof.
    unfold setC, setI, setU.

    apply seteqP.
    split.

  - intros x.
    cbn.
    intro h1.

    destruct (pselect (s1 x)) as [hs1 | not_hs1].
      + right.
        intro hs2.
        apply h1.
        split.

        * exact hs1.
        * exact hs2.

      + left.
        exact not_hs1.

  - intros x.
    (* simpl. *)
    (* cbn. *)
    (* lazy. *)
    cbv.
