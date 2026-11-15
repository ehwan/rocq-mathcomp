From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau derive sequences realfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Import Num.Def Num.Theory.

From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section sequence.
Context (R: realType).
Definition geometric_arithmetic (a r: R) := [sequence a*(r^+n)*+n]_n.

Theorem cvg_geometric_arithmetic (a r: R) :
  `|r| < 1 -> geometric_arithmetic a r @\oo --> 0.
Proof.
move=> radius.
pose q:R := (`|r| + 1)/2.
pose t:R := `|r| / q.
pose C:R := `|a| / ( 1 - t ).

have rnorm_ge0 := normr_ge0 r.
have q_bounds : `|r| < q < 1.
- rw /q.
  by lra.
have tq : t * q = `|r|.
- rw /t.
  have q_neq : q != 0 by lra.
  by field.
have t_bounds : 0 <= t < 1 by nra.
have tn_ge0 n : 0 <= t^+n.
- apply: exprn_ge0.
  by lra.
have cvg_X : C * q^+n @[n --> \oo] --> 0.
- rw -(mulr0 C).
  apply: cvgMl_tmp.
  apply: cvg_expr.
  rw ger0_norm.
  + by lra.
  + by lra.

have series_range n :
    -(C * q^+n) <= geometric_arithmetic a r n <= C * q^+n.
- rw -ler_norml.
  rw /geometric_arithmetic /=.
  rw normrMn normrM.
  have partial_bound :
      `|a| * `|r^+n| *+ n <= `|a| * (\sum_(i < n) t^+i) * q^+n.
  + rw -mulrA -mulrnAr.
    apply: ler_wpM2l.
    * exact: normr_ge0.
    rw normrX.
    rw -tq.
    rw exprMn.
    rw -mulrnAl.
    apply: ler_wpM2r.
    * apply: exprn_ge0.
      by lra.
    elim: n => [|n IH].
    * rw expr0.
      rw big_ord0.
      by lra.
    * rw big_ord_recr /=.
      rw -mulr_natr -natr1.
      rw -mulr_natr in IH.
      have tn_step : t^+n.+1 <= t^+n.
      - rw exprS.
        have := tn_ge0 n.
        by nra.
      have := ler0n R n.
      by nra.
  apply: le_trans.
  + exact: partial_bound.
  + clear partial_bound.
    apply: ler_wpM2r.
    * apply: exprn_ge0.
      by lra.
    rw /C.
    apply: ler_wpM2l.
    * exact: normr_ge0.
    rw -div1r.
    rw ler_pdivlMr.
    * by lra.
    have geom_sum : (\sum_(i < n) t^+i) * (1 - t) = 1 - t^+n.
    * elim: n => [|n IH].
      - rw big_ord0.
        rw expr0.
        by ring.
      - rw big_ord_recr /=.
        rw exprSr.
        by nra.
    rw geom_sum.
    have := tn_ge0 n.
    by lra.
apply: squeeze_cvgr.
- apply: nearW.
  exact: series_range.
- rw -oppr0.
  apply: cvgN.
  exact: cvg_X.
- exact: cvg_X.
Qed.

End sequence.
