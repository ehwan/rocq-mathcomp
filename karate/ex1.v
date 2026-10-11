From mathcomp Require Import all_ssreflect.

Lemma axiomS (A B C : Prop) :
  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
    move=> f.
    move=> g.
    move=> a.
    apply: f.
    apply: a.
    apply: g.
    apply: a.
Qed.

Lemma Ex223 (P Q R : Prop) :
  (P -> Q) -> ((Q -> R) -> (P -> R)).
Proof.
    move => a.
    move => b.
    move => c.
    apply: b.
    apply: a.
    exact: c.
Qed.

Lemma double_negation (b : bool) :
  ~~ ~~ b = b.
Proof.
  case: b.
  - by [].
  - by [].
Qed.

Lemma Ex241 :
    forall a b : bool,
  (~~b ==> ~~a) ==> (a ==> b).
Proof.
    move => a b.
    case: a.
    -
        case b.
        - by [].
        - by [].
    -
        by case b.
Qed.

