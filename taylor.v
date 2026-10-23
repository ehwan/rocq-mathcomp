From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau derive sequences.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Import Num.Def Num.Theory.

(* From Coq Require Import Reals. *)
From mathcomp Require Import ring lra field arithmetic_tactic.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section sequence.
Context (R: realType).
Definition geometric_arithmetic (a r: R) := [sequence a*(r^+n)*+n]_n.

Theorem cvg_geometric_arithmetic (a r: R) :
  `|r| < 1 -> geometric_arithmetic a r @\oo --> 0.
Proof.
move=> radius.
(* cbn. *)
(* apply: norm_cvg0. *)
pose q:R := (`|r| + 1)/2.
pose t:R := `|r| / q.
pose C:R := `|a| / ( 1 - t ).

have rnorm_ge0:= (normr_ge0 r).

have q_gt_rnorm: q > `|r|.
- rewrite /q.
  by lra.

have q_lt1: q < 1.
- rewrite /q.
  by lra.

have t_ge0: t >= 0.
- rewrite /t.
  rewrite ler_pdivlMr.
  lra.
  by lra.

have t_lt1: t < 1.
- rewrite /t.
  rewrite ltr_pdivrMr.
  lra.
  by lra.

have tn_ge0 (n: nat): t^+n >= 0.
- by rewrite exprn_ge0 //=.

have r_eq_tq: `|r| = t * q.
- rewrite /t.
  rewrite divfK //=.
  by lra.

(* for squeeze theorem *)
have cvg_X: C * q^+n @[n --> \oo] --> 0.
- rewrite -(mulr0 C).
  apply: cvgMl_tmp.
  apply: cvg_expr.
  rewrite ger0_norm //=.
  by lra.

have cvg_nX: -(C * q^+n) @[n --> \oo] --> 0.
- rewrite -oppr0.
  apply: cvgN.
  by apply: cvg_X.

(* squeeze theorem le_trans *)
have LE0 (n: nat): geometric_arithmetic a r n <= `|a| * `|r^+n| *+ n.
- rewrite /geometric_arithmetic.
  cbn.
  rewrite -normrM.
  rewrite -normrMn.
  by apply: ler_norm.

have LE1 (n: nat): `|a| * `|r^+n| *+ n <= `|a| * (\sum_(i < n) t^+i) * q^+n.
- rewrite -mulrA -mulrnAr.
  apply: ler_wpM2l.
  + by apply: normr_ge0.
  rewrite normrX r_eq_tq exprMn -mulrnAl.
  apply: ler_wpM2r.
  + apply: exprn_ge0. 
    by lra.

  elim: n.
  + rewrite expr0.
    by rewrite big_ord0.
  + move=> n IH.
    apply: le_trans.
    * apply: (_: t^+n.+1 *+ n.+1 <= t^+n *+ (n.+1)).
      - rewrite ler_pMn2r //=.
        rewrite -[t^+n]mul1r.
        rewrite exprS.
        rewrite ler_wpM2r //=.
        by lra.
    * rewrite big_ord_recr //=.
      rewrite mulrSr.
      rewrite lerD2r.
      by exact: IH.

have geometric_series_mult (n: nat): (\sum_(i < n)  t ^+ i) * (1 - t) = 1 - t^+n.
- elim: n.
  + rewrite big_ord0 //=.
    rewrite expr0.
    by field.
  + move=> n IH.
    rewrite big_ord_recr //=.
    rewrite mulrDl.
    rewrite IH.
    rewrite exprSr.
    by field.

have LE2 (n: nat): `|a| * (\sum_(i < n) t^+i) * q^+n <= C * q^+n.
- rewrite ler_wpM2r //=.
  + apply: exprn_ge0.
    by lra.
  rewrite /C ler_wpM2l //=.

  rewrite -div1r ler_pdivlMr.
  + by lra.

  have tn_ge0':= (tn_ge0 n).
  rewrite geometric_series_mult.
  by lra.

have LE3 (n: nat): -(`|a| * `|r^+n| *+ n) <= geometric_arithmetic a r n.
- rewrite /geometric_arithmetic.
  cbn.
  rewrite -normrM.
  rewrite -normrMn.
  by apply: lerNnormlW.


have LE4 (n: nat): -(`|a| * (\sum_(i < n) t^+i) * q^+n) <= -(`|a| * `|r^+n| *+ n).
- rewrite lerN2.
  by apply: LE1.


have LE5 (n: nat): -(C * q^+n) <= -(`|a| * (\sum_(i < n) t^+i) * q^+n).
- rewrite lerN2.
  by apply: LE2.

apply: squeeze_cvgr.
- apply: nearW.
  move=> n.
  apply /andP.
  split.
  + apply: le_trans.
    * apply: le_trans.
      - by apply: LE5.
      - by apply: LE4.
    * by apply: LE3.
  + apply: le_trans.
    * apply: le_trans.
      - by apply: LE0.
      - by apply: LE1.
    * by apply: LE2.
- by apply: cvg_nX.
- by apply: cvg_X.
Qed.

End sequence.


Section taylor_coeff.
Context (R: realType).
Context (f: R -> R).

Definition taylor_coeff (n: nat) (a: R) : R->R :=
    (cst (f^`(n) a)) * (cst n`!%:R^-1) * (id - cst a)^+n.

Notation "`T_ n '[' a ']'" := (taylor_coeff n a).

Lemma term_nth_0 (n: nat) (x: R) :
    (n > 0)%N -> `T_n[x] x = 0.
Proof.
move=> nge0.
rewrite /taylor_coeff.
rewrite !fctE.
rewrite subrr.
rewrite expr0n.
by rewrite (gtn_eqF nge0) /= mulr0.
Qed.

Lemma taylor_coeff0 (a x: R) :
    `T_0[a] x = f a.
Proof.
rewrite /taylor_coeff.
rewrite !fctE.
rewrite fact0 //=.
rewrite expr0.
by rewrite mulr1 divr1.
Qed.

End taylor_coeff.





Section taylor_theorem.
Context (R: realType).
Context (f: R -> R).
Context (k: nat).
Context (a: R).
Context (F_Derivable: forall (n: nat), (n<=k.+1)%N -> derivable (derive1n n f) a 1).

Notation "`T_ n '[' x ']'" := (taylor_coeff f n x).


(* TODO: use notation *)
Lemma term_nth_derivable (n: nat) (x: R) :
    (n<=k.+1)%N -> derivable (taylor_coeff f n x) a 1.
Proof.
move=> nlek.
unfold taylor_coeff.

apply derivableM.
- apply derivableM.
  + by apply: (F_Derivable nlek).
  + by apply derivable_cst.
- apply derivableX.
  apply derivableB.
  + by apply derivable_cst.
  + by apply derivable_id.
Qed.

Lemma remainder_nth_derivate_eq (n: nat) (x: R) :
    (n<=k.+1)%N -> (cst (f x) - \sum_(i < n.+1) taylor_coeff f i x)^`() = - f^`(n+1) * cst n`!%:R^-1 * (cst x - id)^+n.
Proof.
move=> nlek.
apply eq_fun.
move=> a'.
Search (_^`()).
rewrite derive1E //=.
Search "deriveB".
rewrite deriveB.
apply derivable_cst.
Search derivable "sum".
apply derivable_sum.
move=> i.
apply term_nth_derivable.
Search derive "cst".
rewrite derive_cst.
rewrite sub0r.
rewrite !fctE.
Check oppr_inj.
Check congr1.
apply: oppr_inj.
rewrite !mulNr.
rewrite !opprK.
rewrite derive_sum.
move=> i.
apply term_nth_derivable.


unfold taylor_coeff.
Search "derive" "*".
Check eq_bigr.
under eq_bigr.
    move=> i _.
    rewrite deriveM.
    apply derivableM.
    apply F_Derivable.
    apply derivable_cst.
    Search derivable (_^+_)%R.
    apply derivableX.
    apply derivableB.
    apply derivable_cst.
    apply derivable_id.

    Search derive.
    rewrite deriveX.
    apply derivableB.
    apply derivable_cst.
    apply derivable_id.

    Search derive.
    rewrite deriveB.
    apply derivable_cst.
    apply derivable_id.

    rewrite derive_cst.
    rewrite derive_id.

    rewrite deriveM.
    apply F_Derivable.
    apply derivable_cst.
    rewrite derive_cst.

    Search "derive".
    rewrite -derive1E.
    rewrite -derive1nS.

    Search (0 - _).
    rewrite sub0r.
    Search (-1*_).
    rewrite !/cst.
    rewrite !fctE /=.
    rewrite [(i%:R * (x - a) ^+ i.-1) *: -1]mulrC.
    rewrite mulNr.
    rewrite mul1r.
    Search (_*-_).
    rewrite scalerN.
    rewrite scaler0.
    rewrite add0r.
over.
simpl.

elim: n.
    Check big_ord1.
    rewrite big_ord1 //=.
    rewrite !fact0.
    rewrite !divr1.
    rewrite !mul0r.
    rewrite !scaler0.
    Search (_^+0).
    rewrite !expr0.
    rewrite !mulr1.
    Search (1^+_).
    Search (1^-1).
    rewrite invr1.
    rewrite !scale1r.
    rewrite addrC.
    rewrite subr0.
    exact.

    move=> n.
    move=> IH.
    rewrite big_ord_recr //=.
    rewrite IH.
    rewrite -derive1nS.
    Search (_ + 1 = _.+1)%N.
    rewrite !addn1.
    set FFN := f^`(n.+1).
    set NF := n`!%:R.
    set XA := x-a.
    set NNF := (n.+1)`!%:R.
    rewrite !addrA.
    rewrite !scalerA.
    rewrite -[FFN a / NNF * n.+1%:R]mulrA.
    rewrite /GRing.scale /=.
    have n1_neq0 : n.+1%:R != 0 :> R.
        by rewrite pnatr_eq0.

    have NNF_E : NNF = n.+1%:R * NF.
        by rewrite /NNF /NF factS natrM.
    have coeffE : NNF^-1 * n.+1%:R = NF^-1.
        rewrite NNF_E.
        rewrite invfM.
        (* rewrite [NF^-1 * n.+1%:R]mulrC. *)
        (* rewrite mulrA. *)
        rewrite -mulrA.
        rewrite [NF^-1 * n.+1%:R]mulrC.
        rewrite mulrA.
        Check mulVf.
        rewrite mulVf.
        exact n1_neq0.
        apply: div1r.

    rewrite coeffE.
    rewrite subrr.
    rewrite add0r.
    rewrite mulrC.
    rewrite [XA ^+ n.+1 / NNF]mulrC.
    rewrite !mulrA.
    exact.
Qed.



Lemma remainder_nth0_eq (n: nat) (x: R):
    f x - (\sum_(i < n.+1) taylor_coeff f i x) x = 0.
Proof.
    induction n.

    Check big_ord1.
    Search "big_ord".
    rewrite big_ord1 //=.
    (* rewrite !fctE. *)
    rewrite term_0th.
    rewrite addrN.
    exact.

    rewrite big_ord_recr //=.
    rewrite !fctE.
    rewrite term_nth_0 //=.

    rewrite addr0.
    exact IHn.
Qed.

Lemma remainder_eq (n: nat) (x a: R) :
    exists xi: R,
    f x - \sum_(i < n.+1) taylor_coeff f i x a = (f^`(n+1) xi) * n`!%:R^-1 * (x - xi)^+n * (x - a) 
    /\
    xi \in `[minr x a, maxr x a]%R.
Proof.
    have remainder_nth_derivable : forall x0: R, derivable (cst (f x) - \sum_(i < n.+1)  taylor_coeff f i x) x0 1.
        move=> x0.
        apply derivableB.
        apply derivable_cst.
        apply derivable_sum.
        move=> i.
        apply term_nth_derivable.

    pose G := cst (f x) - \sum_(i < n.+1) taylor_coeff f i x.
    Check derive1n.
    pose dG := derive1n 1 G.

    have G_MVT_Segment: forall (min max: R), min <= max ->
        exists2 xi : R, xi  \in `[min, max]%R & G max - G min = dG xi * (max - min).
        move=> min max.
        move=> minmax.
        apply MVT_segment.
        exact minmax.

        move=> x0 _.
        Search "is_derive".
        Search "derive1".
        Search "derivable".
        rewrite /dG.
        rewrite derive1n1.
        rewrite derive1E.
        apply derivableP.
        rewrite /G.
        apply remainder_nth_derivable.

        Search derivable "cont".
        apply derivable_within_continuous.
        move=> x0 _.
        rewrite /G.
        apply remainder_nth_derivable.

    have MVT_G_eq: forall xi: R,
        G x - G a = dG xi * (x - a) ->
        f x - \sum_(i < n.+1)  taylor_coeff f i x a = f^`(n + 1) xi / n`!%:R * (x - xi) ^+ n * (x - a).
        move=> xi.
        (* move=> mvt. *)
        unfold dG.
        rewrite derive1n1.
        unfold G.
        rewrite remainder_nth_derivate_eq //.
        rewrite !fctE.
        rewrite remainder_nth0_eq.
        rewrite sub0r.
        rewrite !mulNr.
        rewrite fct_sumE.
        apply: oppr_inj.

    case: (lerP a x).
    - {
        move=> ax.
        have MVT_segment_res : 
            exists2 xi : R, xi  \in `[a, x]%R & G x - G a = dG xi * (x - a).
            apply: (G_MVT_Segment a x).
            exact ax.
        
        destruct MVT_segment_res as [xi xi_range xi_mvt].
        exists xi.
        split.
        apply: MVT_G_eq.
        exact xi_mvt.

        (* xi in `[minr x a, maxr x a]%R *)
        exact xi_range.
    }
    - {
        move=> Hxa.
        have xa: x <= a.
            apply: (ltW Hxa).
        Check MVT.
        have MVT_segment_res : 
            exists2 xi : R, xi  \in `[x, a]%R & G a - G x = dG xi * (a - x).
            apply: (G_MVT_Segment x a).
            exact xa.

        destruct MVT_segment_res as [xi xi_range xi_mvt].
        exists xi.
        split.
        have xi_mvt': G x - G a = dG xi * (x - a).
            rewrite -[(G x - G a)]opprB.
            rewrite -[(x - a)]opprB.
            rewrite mulrN.
            apply: oppr_inj.
            rewrite !opprK.
            exact xi_mvt.
        
        apply: MVT_G_eq.
        exact xi_mvt'.

        (* xi in `[minr x a, maxr x a]%R *)
        exact xi_range.
    }
Qed.

Theorem taylor_theorem :
    exists h: R->R,
        (forall (x: R),
            (h x) * (x-a)^+k = f x - \sum_(i < k.+1) taylor_coeff f i x a)
        /\
        h x @[x --> a] --> 0.
Proof.
    (* h x @[x-->a] --> 0 *)

    have [xi_x H_xi_x]:=
        @choice R R
            _
            (fun x => remainder_eq k x a).

    pose h_x:= fun x: R =>
        if x == a then 0
        else (f x - \sum_(i < n.+1) taylor_coeff f i x a) / (x-a)^+n.
    exists h_x.

    split.
    move=> x.
    rewrite /h_x.
    case: eqP.
    move=> xa.
    rewrite mul0r.
    rewrite (_: \sum_(i < n.+1)  taylor_coeff f i x a = (\sum_(i < n.+1)  taylor_coeff f i x) x).
        rewrite fct_sumE //=.
        rewrite xa.
        exact.
    rewrite remainder_nth0_eq.
    exact.

    move=> xa_neq.
    field?.
    apply: expf_neq0.
    lra.

    apply/cvgrPdist_lt => eps eps_gt0.

    have [C HC] := F_Analytic3 (a - eps) (a + eps).

    pose K := `|C ^+ (n.+2)| * (n.+1)%:R.
    pose D := K + 1.
    pose delta := eps / D.

    have Kge0 : 0 <= K.
        by rewrite /K mulr_ge0 ?normr_ge0 ?ler0n.

    have Dpos : 0 < D.
        rewrite /D.
        lra.
    have Dge1 : 1 <= D.
        rewrite /D.
        lra.

    have delta_pos : 0 < delta.
        rewrite /delta.
        apply: divr_gt0.
        - exact: eps_gt0.
        - exact: Dpos.

    have delta_le_eps : delta <= eps.
        rewrite /delta.
        rewrite ler_pdivrMr //=.
        nra.

    have Ddelta : D * delta = eps.
        rewrite /delta.
        field?.
        lra.

    exists delta.
    rewrite //=.
    move=> x.
    rewrite //=.
    rewrite -normrN opprB.
    rewrite /delta ltr_pdivlMr.
    lra.
    rewrite mulrC.
    rewrite /D.
    (* rewrite /D. *)
    move=> xa_lt_delta.
    have kxa_lt_epsilon: (K * `|x - a| < eps).
        nra.
    have xa_lt_epsilon: (`|x-a| < eps).
        nra.
    have xa_range: x \in `[a-eps, a+eps]%R.
        rewrite ler_radius_itv ltW //=.
    rewrite in_itv //= in xa_range.

    rewrite sub0r.
    rewrite normrN.
    apply: le_lt_trans.
    apply: (_: `|h_x x| <= K * `|x - a|).
        rewrite /h_x.
        case: eqP.

        (* x = a *)
        move=> xa.
        rewrite normr0.
        rewrite xa.
        rewrite subrr normr0 mulr0 //=.


        (* x != a *)
        move/eqP=> xaneq.
        have [H_xi xi_in_range]:= H_xi_x x.
        have xi_range := in_itv_inequality xi_in_range.
        rewrite H_xi //=.
        rewrite !normrM.
        set F:= f^`(n+1) (xi_x x).
        set NF:= n`!%:R.
        set XXI:= x - xi_x x.
        set XA:= x - a.
        have xxi_xa: `|XXI| <= `|XA|.
            rewrite /XXI /XA.
            (* |x - xi| <= |x - a| *)
            case: (lerP a x).
                (* a <= x *)
                move=> xa.
                move: (xi_in_range).
                rewrite /minr /maxr in_itv //=.
                rewrite ltNge.
                rewrite xa //=.
                move=> /andP [axi xix].
                rewrite /XXI.
                rewrite ger0_norm.
                rewrite lerBrDr add0r.
                exact xix.
                rewrite lerD //=.
                Search "ler" "N".
                rewrite lerNr opprK.
                exact axi.

                (* x < a *)
                move=> xa.
                move: (xi_in_range).
                rewrite /minr /maxr in_itv //=.
                rewrite xa.
                move=> /andP [axi xix].
                rewrite /XXI.
                rewrite ler0_norm.
                rewrite lerBlDl addr0.
                exact axi.
                rewrite opprB.
                rewrite lerD //=.
        have nFge0: `|F| >= 0.
            apply: normr_ge0.
        rewrite (_: `|F| * `|NF^-1| * `|XXI ^+ n| * `|XA| * `|XA ^- n| = `|F| * `|NF^-1| * `|XA| * `|XA ^- n| * `|XXI ^+ n|).
            field.
        apply: le_trans.
            apply: (_: `|F| * `|NF^-1| * `|XA| * `|XA ^- n| * `|XXI ^+ n| <= `|F| * `|NF^-1| * `|XA| * `|XA ^- n| * `|XA^+ n|).
                rewrite !normrX.
                rewrite ler_wpM2l.
                rewrite -!normrM.
                apply: normr_ge0.
                rewrite lerXn2r //=.
                apply: normr_ge0.
                apply: normr_ge0.
                exact.

            rewrite -mulrA.
            rewrite -[`|XA ^- n| * `|XA ^+ n|]normrM.
            rewrite (_: XA ^- n * XA ^+ n = 1).
                rewrite mulVf.
                rewrite expf_neq0.
                rewrite subr_eq0 //=.
                exact.
                exact.
            
            rewrite normr1.
            rewrite mulr1.
            apply: ler_wpM2r.
            apply: normr_ge0.
            rewrite /K.
            have xi_in_eps_range: xi_x x  \in `[a - eps, a + eps].
                rewrite inE.
                have [_ radius_form]:= (ler_radius_itv (xi_x x) a eps).
                apply: radius_form.
                apply: le_trans.

                apply: (_: (`|xi_x x - a| <= `|x-a|)).
                    case: (lerP a x).

                    move=> ax.
                    rewrite (_: (minr x a) = a) in xi_range.
                    apply/min_idPr.
                    exact ax.
                    rewrite ger0_norm //=.
                    lra.
                    rewrite (_: (maxr x a) = x) in xi_range.
                    apply/max_idPl.
                    exact ax.
                    lra.

                    move=> xa.
                    rewrite (_: (minr x a) = x) in xi_range.
                    rewrite /minr //=.
                    rewrite (_: x<a = true) //=.
                    rewrite (_: (maxr x a) = a) in xi_range.
                    rewrite /maxr //=.
                    rewrite (_: x<a = true) //=.
                    rewrite ler0_norm //=.
                    lra.
                    lra.
                rewrite ltW //=.

            have HC_x := HC (n.+1) (xi_x x) xi_in_eps_range.
            rewrite [`|NF^-1|]ger0_norm.
            rewrite invr_ge0.
            rewrite ler0n //=.
            rewrite ler_pdivrMr.
            rewrite ltr0n.
            apply: fact_gt0.
            rewrite /NF.
            rewrite -[`|C ^+ n.+2| * n.+1%:R * n`!%:R]mulrA.
            rewrite -natrM.
            rewrite -factS.
            rewrite [`|C ^+ n.+2|]ger0_norm.
            move: (HC_x).
            rewrite -ler_pdivrMr //=.
            rewrite -[(n.+1)`!%:R]ger0_norm //=.
            rewrite -normf_div.
            apply: le_trans.
            apply: normr_ge0.
            rewrite /F.
            rewrite addn1.
            exact HC_x.
            rewrite //=.
Qed.










(* taylor analytic *)
Section taylor_analytic.
Context (R: realType).
Context (f: R -> R).
Context (F_Derivable: forall (n:nat) (x: R), derivable (derive1n n f) x 1).
Context (F_Analytic3: forall (a b: R), exists C: R, forall (k: nat), {in `[a, b], forall x, `|f^`(k) x| <= C^+k.+1 * k`!%:R}).
Notation "`T_ n '[' a ']'" := (taylor_coeff f n a).



Lemma in_itv_inequality (a b x: R):
    x \in `[a, b]%R -> 0 <= x - a <= b - a /\ 0 <= b - x <= b - a.
Proof.
    rewrite in_itv //=.
    lra.
Qed.

Lemma ler_radius_itv (a b radius: R):
    (a \in `[b-radius, b+radius]%R) <-> (`|a - b| <= radius).
Proof.
    rewrite in_itv //=.
    case: (lerP a b).
    lra.
    lra.
Qed.



(* C * |x-a| < 1 *)
Theorem taylor_theorem2 (a x: R) :
    exists Radius: R ,
        Radius > 0 ->
        `|x - a| < Radius
        -> (fun n => f x - \sum_(i < n.+1) taylor_coeff f i x a) @\oo --> 0.
Proof.
    pose range_min := minr x a.
    pose range_max := maxr x a.

    have [C H_C] := F_Analytic3 range_min range_max.

    pose Radius:= 1 / C.
    exists Radius.
    rewrite /Radius.
    rewrite div1r invr_gt0.
    move=> C_GT0.
    rewrite -div1r ltr_pdivlMr.
    exact C_GT0.
    rewrite mulrC.
    move=> xa_radius.

    have [xi_n H_xi_n]:=
        @choice nat R
            _
            (fun n => remainder_eq n x a).

    pose remainder_xi := fun n => (f^`(n+1) (xi_n n)) * n`!%:R^-1 * (x - (xi_n n))^+n * (x - a).
    rewrite (_: (fun n => f x - \sum_(i < n.+1) taylor_coeff f i x a) = remainder_xi).
        rewrite /remainder_xi.
        apply eq_fun.
        move=> n.
        case: (H_xi_n n) => [H_xi_ _].
        exact H_xi_.

    pose X_n := fun n: nat =>  C * (n+1)%:R * (C* `|(x-a)|)^+(n+1).

    have X_cvgr : X_n @\oo --> 0.
        rewrite (_: X_n = fun (n: nat) => C * [sequence (nxn_sequence (C * `|x-a|)) (n.+1)]_n n).
            rewrite /X_n.
            apply: eq_fun.
            move=> n.
            rewrite /nxn_sequence.
            rewrite !mulrA.
            rewrite !addn1.
            exact.

        rewrite -(mulr0 C).
        apply: cvgMl_tmp.
        rewrite cvg_shiftS //=.
        apply: cvg_nxn.
        rewrite normrM.
        rewrite ger0_norm.
        rewrite ltW //=.
        rewrite ger0_norm.
        apply: normr_ge0.
        apply: xa_radius.

    have XN_cvgr : -X_n @\oo --> 0.
        Search "cvg" "-".
        Search (-0 = 0).
        rewrite -oppr0.
        apply: cvgN.
        apply: X_cvgr.

    have F_range : forall n: nat, -X_n n <= remainder_xi n <= X_n n.
        move=> n.
        case: (H_xi_n n) => [_ xi_in_range].

        set F := f^`(n+1) (xi_n n).
        set XXI := (x - xi_n n).
        set XA := x-a.
        pose N:R := n`!%:R.

        have LE0: F / N * XXI^+n * XA <= `|F| * `|N^-1| * `|XXI^+n| * `|XA|.
            rewrite -!normrM.
            apply: ler_norm.

        have LE1: `|F| * `|N^-1| * `|XXI^+n| * `|XA| <= C^+(n+2) * (n+1)%:R * `|XXI^+n| * `|XA|.
            apply: ler_wpM2r.
            apply: normr_ge0.
            apply: ler_wpM2r.
            apply: normr_ge0.
            Check ler_wpM2r.
            rewrite -(ler_pM2r (x:= N)).
            Search "fact" "gt".
            rewrite /N ltr0n.
            apply: fact_gt0.

            (* `|N^-1| * N *)
            Search "normr" "M".
            Search (_ = `|_|).
            Search "normr".
            Search (0 < _ -> `|_| = _).
            rewrite -{2}(gtr0_norm (x:=N)).
            rewrite /N ltr0n.
            apply: fact_gt0.

            (* `|N^-1| * `|N| = `|N^-1 * N| *)
            rewrite -mulrA.
            rewrite -normrM.
            Search (_^-1 * _).
            rewrite mulVf.
            rewrite /N //=.
            rewrite normr1.
            rewrite mulr1.

            (* (n+1) * N = (n+1)! *)
            Search (_%:R * _%:R).
            rewrite /N.
            rewrite -mulrA.
            rewrite -natrM.
            rewrite /F.
            rewrite !addn1 !addn2.
            rewrite -factS.

            apply: H_C.
            rewrite inE.
            apply: xi_in_range.

        have LE2: C^+(n+2) * (n+1)%:R * `|XXI^+n| * `|XA| <= C * (n + 1)%:R * (C * `|XA|)^+(n+1).
            rewrite !addn1 !addn2.
            Search (_^+(S _)).
            rewrite exprS.
            rewrite -!mulrA.
            apply: ler_wpM2l.
            rewrite ltW //=.
            rewrite mulrA.
            rewrite -[C ^+ n.+1 * n.+1%:R]mulrC.
            rewrite -mulrA.
            apply: ler_wpM2l.
            rewrite ler0n //=.

            (*  (C * `|XA|) ^+ n.+1 *)
            rewrite exprMn.
            apply: ler_wpM2l.
            apply: exprn_ge0.
            rewrite ltW //=.
            rewrite exprSr.
            apply: ler_wpM2r.
            apply: normr_ge0.
            rewrite normrX.
            apply: lerXn2r.
            apply: normr_ge0.
            apply: normr_ge0.

            (* |x - xi| <= |x - a| *)
            have xi_range := in_itv_inequality xi_in_range.
            case: (lerP a x).
                (* x >= a *)
                move=> ax.
                rewrite (_: minr x a = a) in xi_range.
                    rewrite /minr //=.
                    rewrite (_: x<a = false) //=.
                    lra.
                rewrite (_: maxr x a = x) in xi_range.
                    rewrite /maxr //=.
                    rewrite (_: x<a = false) //=.
                    lra.
                rewrite /XXI.
                rewrite ger0_norm.
                lra.
                lra.

                (* x < a *)
                move=> xa.
                rewrite (_: minr x a = x) in xi_range.
                    rewrite /minr //=.
                    rewrite (_: x<a = true) //=.
                rewrite (_: maxr x a = a) in xi_range.
                    rewrite /maxr //=.
                    rewrite (_: x<a = true) //=.
                rewrite /XXI.
                rewrite ler0_norm.
                lra.
                lra.

        have LE3: -(`|F| * `|N^-1| * `|XXI^+n| * `|XA|) <= F / N * XXI^+n * XA.
            rewrite -!normrM.
            apply: lerNnormlW.
            exact.

        have LE4: -(C^+(n+2) * (n+1)%:R * `|XXI^+n| * `|XA|) <= -(`|F| * `|N^-1| * `|XXI^+n| * `|XA|).
            rewrite lerN2.
            apply: LE1.

        have LE5: -(C * (n + 1)%:R * (C * `|XA|)^+(n+1)) <= -(C^+(n+2) * (n+1)%:R * `|XXI^+n| * `|XA|).
            rewrite lerN2.
            apply: LE2.


        apply /andP.
        split.

        (* -X_n n <= remainder_xi n *)
        rewrite /remainder_xi /X_n.
        apply: le_trans.
        apply: le_trans.
        apply: LE5.
        apply: LE4.
        apply: LE3.

        (* remainder_xi n <= X_n n. *)
        rewrite /remainder_xi /X_n.
        apply: le_trans.
        apply: le_trans.
        apply: LE0.
        apply: LE1.
        apply: LE2.

    Check squeeze_cvgr.
    apply: squeeze_cvgr.
    apply: nearW.
    apply: F_range.

    apply: XN_cvgr.
    apply: X_cvgr.
Qed.

End taylor_analytic.
