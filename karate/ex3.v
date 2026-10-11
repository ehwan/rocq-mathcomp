From mathcomp Require Import all_ssreflect.

Check nat_ind.
Search "big" "ind".

Search "big" "0".
Search "big" "geq".

Search ((_*(_+_))%N = _ + _).
Search "muln".
Check mulnDr.
About mulnDr.
Search "addn".

Lemma Ex353 (n : nat) :
    2*\sum_(0<=x <n.+1) x = n * (n.+1).
Proof.
    elim: n.
    - rewrite big_nat_recr //=.
      by rewrite big_geq.
    - move => n IH.
      rewrite big_nat_recr //=.
      rewrite mulnDr.
      rewrite IH.
      rewrite <- mulnDl.
      rewrite mulnC.
      rewrite addn2.
      by [].
Qed.

About big_ind2.
Check big_ind2.
Print Implicit big_ind2.

Search (_ + _ = _).
Search (_ * _ = _).

Lemma Ex354 (n : nat) :
    \sum_(0 <= x < n.+1) (x + x) = 2 * \sum_(0 <= x < n.+1) x.
Proof.
    pose K := fun a b: nat => a = 2 * b.
    pose bigind2 := big_ind2 K.
    apply: bigind2.
    - by [].
    - move => x1 x2 y1 y2.
      move => Hx Hy.
      rewrite /K in Hx Hy *.
      rewrite Hx Hy.
      by rewrite mulnDr.
    - move => i.
      move => _.
      rewrite /K.
      rewrite addnn.
      by rewrite mul2n.
Qed.

Search "big_" "recr".
Search "big_" "0".
Search (_ - _ = _ + _).
Search (_^(_.+1)).
Search "addn".
Search "subn".

Lemma Ex355 (n : nat) :
    \sum_(i < n.+1) 2^i = 2^(n.+1) - 1.
Proof.
    elim: n.
    - rewrite big_ord_recr //=.
      rewrite big_ord0 //=.
    - move => n IH.
      rewrite big_ord_recr //=.
      rewrite IH.
      rewrite [2^n.+2] expnS.
      set x := 2^n.+1.

      Search "addnBA".
      have ge1 : 1 <= x.
      Search (1 <= _ ^ _).
      rewrite expn_gt0 //=.
      Search "addnBA".
      rewrite (addnBAC x ge1).
      Search (_ + _ = _).
      rewrite addnn.
      Search (2 * _).
      by rewrite mul2n.
Qed.

About big_ind.