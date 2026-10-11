From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.
(* From mathcomp Require Import numfield. *)

Search "sqrt".

Lemma Ex361 ( R : rcfType):
    Num.sqrt ((4 : R) + (2 : R) * Num.sqrt (3 : R)) = (1 : R) + Num.sqrt (3 : R).
Proof.
    have h3 : (0 : R) <= 3 by exact: ler0n 3.

    have hright : (0 : R) <= 1 + Num.sqrt 3.
        apply: addr_ge0.
        - exact: ler01.
        - exact: sqrtr_ge0.

have hsq :
    (1 + Num.sqrt 3 : R) ^+ 2 =
    4 + 2 * Num.sqrt 3.
  rewrite sqrrD expr1n mul1r (sqr_sqrtr h3).
  ring.

by rewrite -hsq sqrtr_sqr (ger0_norm hright).
Qed.
