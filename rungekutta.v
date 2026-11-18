From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference.
From mathcomp Require Import sesquilinear.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp contra classical_sets functions reals.
From mathcomp Require Import topology tvs normedtype landau derive sequences
  realfun exp.

From mathcomp Require Import arithmetic_tactic.

Require Import taylor_poly taylor_remainder.

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

Section RK.

Context (R : realType).
Context (f : R -> R -> R) (x0 : R).
Context (alpha beta p q : R).

Section Method.
Context (h : R).

Let t_n (n : nat) := n%:R * h.

Definition rk2_slope (t x1 : R) : R :=
  let k1 := f t x1 in
  let k2 := f (t + p * h) (x1 + q * h * k1) in
  alpha * k1 + beta * k2.

Definition rk2_step (t x1 : R) : R := x1 + h * rk2_slope t x1.

Fixpoint rk2 (n : nat) : R :=
  match n with
  | O => x0
  | S m => rk2_step (t_n m) (rk2 m)
  end.

End Method.

(* Taylor bounds for an increment of either sign. *)
Local Abbreviation between a b := (`[minr a b, maxr a b]%R).

Local Lemma taylor_bound (g : R -> R) (m : nat) (a d M : R)
    (dg : forall k, (k <= m)%N ->
      {in between a (a + d), forall s, derivable (derive1n k g) s 1})
    (bg : {in between a (a + d), forall s, `|derive1n m.+1 g s| <= M}) :
  `|g (a + d) - taylor_sum g m a (a + d)| <= M * `|d| ^+ m.+1.
Proof.
have [s hs ->] := @taylor_remainder_lagrange R g m a (a + d) dg.
rewrite addrAC subrr add0r normrM normf_div normrX.
apply: ler_wpM2r; first exact: exprn_ge0 (normr_ge0 _).
have hf : 1 <= m.+1`!%:R :> R by rewrite ler1n fact_gt0.
have hfpos : 0 < m.+1`!%:R :> R by rewrite ltr0n fact_gt0.
rewrite (ger0_norm (ltW hfpos)) ler_pdivrMr //.
have hb := bg s hs.
have hM := le_trans (normr_ge0 _) hb.
by nra.
Qed.

Local Lemma sqr_normr (u : R) : `|u| ^+ 2 = u ^+ 2.
Proof. by rewrite -normrX ger0_norm // sqr_ge0. Qed.

Local Lemma taylor_linear (g : R -> R) a d :
  taylor_sum g 1 a (a + d) = g a + derive1n 1 g a * d.
Proof.
rewrite taylor_sumS taylor_sum0 /taylor_term !fctE expr1 (_ : 1`! = 1%N) //.
by field.
Qed.

Local Lemma taylor_quadratic (g : R -> R) a d :
  taylor_sum g 2 a (a + d) =
    g a + derive1n 1 g a * d + derive1n 2 g a * d ^+ 2 / 2.
Proof.
rewrite taylor_sumS taylor_linear /taylor_term !fctE.
rewrite (_ : 2`! = 2%N) //.
by field.
Qed.

Section ErrorAnalysis.

Context (x : R -> R) (T : R).
Context (T_pos : 0 < T) (x_initial : x 0 = x0).
Context (weights_sum : alpha + beta = 1).
Context (order_time : beta * p = 1 / 2) (order_state : beta * q = 1 / 2).

Local Abbreviation time_interval := (`[0, T]%R).
Let ft (t x1 : R) := derive1n 1 (fun s => f s x1) t.

(* The exact solution: the ODE and the degree-two Taylor remainder. *)
Context (x_ode : {in time_interval, forall t, derive1n 1 x t = f t (x t)}).
Context (x_derivable : forall k : nat, (k <= 2)%N ->
  {in time_interval, forall t, derivable (derive1n k x) t 1}).
Context (M_x3 : R) (x3_bound :
  {in time_interval, forall t, `|derive1n 3 x t| <= M_x3}).

(* Global slice bounds allow any stage time t + p * h. *)
Context (f_time_derivable : forall (x1 : R) (k : nat), (k <= 1)%N ->
  forall t : R, derivable (derive1n k (fun s => f s x1)) t 1).
Context (f_state_derivable : forall (t : R) (k : nat), (k <= 1)%N ->
  forall x1 : R, derivable (derive1n k (f t)) x1 1).
Context (M_f M_tt M_xx : R).
Context (f_bound : forall t x1, `|f t x1| <= M_f).
Context (ftt_bound : forall t x1, `|derive1n 2 (fun s => f s x1) t| <= M_tt).
Context (fxx_bound : forall t x1, `|derive1n 2 (f t) x1| <= M_xx).

(* Uniform Lipschitz bounds in the state variable. *)
Context (L_f L_ft : R).
Context (f_lipschitz : forall t x1 x2,
  `|f t x1 - f t x2| <= L_f * `|x1 - x2|).
Context (ft_lipschitz : forall t x1 x2,
  `|ft t x1 - ft t x2| <= L_ft * `|x1 - x2|).

Local Lemma L_f_ge0 : 0 <= L_f.
Proof.
have := f_lipschitz 0 1 0; rewrite subr0 normr1 mulr1.
exact: le_trans (normr_ge0 _).
Qed.

Let fx (t x1 : R) := derive1n 1 (f t) x1.
Let slope_derivative t x1 := ft t x1 + fx t x1 * f t x1.
Let stage_constant := M_tt + M_xx * M_f ^+ 2 + L_ft * M_f.

(* Expand the two coordinate slices separately, keeping the first slope fixed. *)
Lemma rk2_stage_remainder t x1 d :
  `|f (t + d) (x1 + d * f t x1) - (f t x1 + d * slope_derivative t x1)|
    <= stage_constant * d ^+ 2.
Proof.
pose v := f t x1.
pose w := x1 + d * v.
have et := @taylor_bound (fun s => f s w) 1 t d M_tt
  (fun k hk s _ => @f_time_derivable w k hk s) (fun s _ => ftt_bound s w).
have ex := @taylor_bound (f t) 1 x1 (d * v) M_xx
  (fun k hk s _ => @f_state_derivable t k hk s) (fun s _ => fxx_bound t s).
rewrite taylor_linear in et.
rewrite taylor_linear in ex.
have em := ft_lipschitz t w x1.
have dw : w - x1 = d * v by rewrite /w; ring.
rewrite dw normrM in em.
have bv : `|v| <= M_f := f_bound t x1.
have hxx := le_trans (normr_ge0 _) (fxx_bound t x1).
have hL : 0 <= L_ft.
  have := ft_lipschitz t 1 0.
  rewrite subr0 normr1 mulr1.
  exact: le_trans (normr_ge0 _).
have bv2 : `|v| ^+ 2 <= M_f ^+ 2 by have := normr_ge0 v; nra.
have ex' : `|f t w - (v + fx t x1 * (d * v))| <=
    M_xx * M_f ^+ 2 * d ^+ 2.
  apply: le_trans ex _.
  rewrite normrM exprMn !sqr_normr.
  have hs := ler_wpM2l hxx bv2.
  rewrite sqr_normr in hs.
  have := ler_wpM2r (sqr_ge0 d) hs.
  by nra.
have em' : `|(ft t w - ft t x1) * d| <= L_ft * M_f * d ^+ 2.
  rewrite normrM.
  apply: le_trans (ler_wpM2r (normr_ge0 d) em) _.
  have h := ler_wpM2l hL bv.
  have := ler_wpM2r (sqr_ge0 `|d|) h.
  rewrite -[d ^+ 2]sqr_normr.
  by nra.
rewrite sqr_normr in et.
have -> : f (t + d) (x1 + d * f t x1) - (f t x1 + d * slope_derivative t x1) =
    (f (t + d) w - (f t w + ft t w * d)) +
    (f t w - (v + fx t x1 * (d * v))) + (ft t w - ft t x1) * d.
  rewrite /slope_derivative /v /w; ring.
apply: le_trans (ler_normD _ _) _.
have tri := ler_normD (f (t + d) w - (f t w + ft t w * d))
                      (f t w - (v + fx t x1 * (d * v))).
have et' : `|f (t + d) w - (f t w + ft t w * d)| <= M_tt * d ^+ 2 := et.
rewrite /stage_constant [(_ + _ + _) * d ^+ 2]mulrDl [(_ + _) * d ^+ 2]mulrDl.
exact: lerD (le_trans tri (lerD et' ex')) em'.
Qed.

(* The order conditions match the linear term in the weighted stage slopes. *)
Lemma rk2_slope_remainder t x1 h :
  `|rk2_slope h t x1 - (f t x1 + h / 2 * slope_derivative t x1)| <=
    `|beta| * (stage_constant * (p * h) ^+ 2).
Proof.
have bp0 : beta != 0 by apply/eqP => b0; move: (order_time); rewrite b0 mul0r; lra.
have pq : p = q by apply: (mulfI bp0); rewrite order_time order_state.
pose v := f t x1.
pose A := slope_derivative t x1.
pose k2 := f (t + p * h) (x1 + p * h * v).
have stage : `|k2 - (v + p * h * A)| <= stage_constant * (p * h) ^+ 2 :=
  rk2_stage_remainder t x1 (p * h).
rewrite /rk2_slope -pq -/v -/k2 -/A.
have -> : alpha * v + beta * k2 - (v + h / 2 * A) = beta * (k2 - (v + p * h * A)).
  have wa : alpha = 1 - beta by move: (weights_sum); lra.
  have scale : beta * (k2 - (v + p * h * A)) =
      beta * k2 - beta * v - (beta * p) * h * A by ring.
  rewrite wa scale order_time; field.
rewrite normrM.
exact: (ler_wpM2l (normr_ge0 beta) stage).
Qed.

Local Lemma solution_taylor (g : R -> R) m a d M :
  (forall k, (k <= m)%N ->
    {in time_interval, forall t, derivable (derive1n k g) t 1}) ->
  {in time_interval, forall t, `|derive1n m.+1 g t| <= M} ->
  a \in time_interval -> a + d \in time_interval ->
  `|g (a + d) - taylor_sum g m a (a + d)| <= M * `|d| ^+ m.+1.
Proof.
move=> dg bg ha hb.
have inside s : s \in between a (a + d) -> s \in time_interval.
  move: ha hb; rewrite !in_itv /= => /andP [a0 aT] /andP [b0 bT] /andP [lo hi].
  apply/andP; split.
  - apply: le_trans _ lo; by rewrite le_min a0 b0.
  - apply: le_trans hi _; by rewrite ge_max aT bT.
exact: (@taylor_bound g m a d M (fun k hk s hs => dg k hk s (inside s hs))
                                (fun s hs => bg s (inside s hs))).
Qed.

Let M_x2 := `|derive1n 2 x 0| + M_x3 * T.

Local Lemma x2_bound : {in time_interval, forall t, `|derive1n 2 x t| <= M_x2}.
Proof.
move=> t ht.
have h0 : 0 \in time_interval by rewrite in_itv /= lexx (ltW T_pos).
have ht' : 0 + t \in time_interval by rewrite add0r.
have dg k : (k <= 0)%N ->
    {in time_interval, forall s, derivable (derive1n k (derive1n 2 x)) s 1}.
  by case: k => // _; exact: (@x_derivable 2 (leqnn 2)).
have b := @solution_taylor (derive1n 2 x) 0 0 t M_x3 dg x3_bound h0 ht'.
rewrite add0r taylor_sum0 expr1 in b.
move: ht; rewrite in_itv /= => /andP [t0 tT].
rewrite (ger0_norm t0) in b.
have m0 := le_trans (normr_ge0 _) (@x3_bound 0 h0).
have tri := ler_normD (derive1n 2 x t - derive1n 2 x 0) (derive1n 2 x 0).
rewrite subrK in tri.
rewrite /M_x2 addrC.
exact: le_trans tri (lerD (le_trans b (ler_wpM2l m0 tT)) (lexx _)).
Qed.

(* Compare the numerical slope to x' at the midpoint, where the ODE holds. *)
Let local_constant := M_x3 + (L_f * M_x2 + stage_constant) / 4 +
                      `|beta| * stage_constant * p ^+ 2.

Lemma rk2_local_error t h :
  0 <= t -> 0 < h -> t + h <= T ->
  `|rk2_step h t (x t) - x (t + h)| <= local_constant * h ^+ 3.
Proof.
move=> t0 hpos endT.
pose d := h / 2.
pose mid := t + d.
have d0 : 0 <= d by rewrite /d; lra.
have ht : t \in time_interval by rewrite in_itv /=; apply/andP; split; lra.
have hm : mid \in time_interval.
  rewrite /mid /d in_itv /=; apply/andP; split; lra.
have he : t + h \in time_interval by rewrite in_itv /=; apply/andP; split; lra.
have quad a s (ha : a \in time_interval) (hb : a + s \in time_interval) :=
  @solution_taylor x 2 a s M_x3 x_derivable x3_bound ha hb.
have plus : mid + d = t + h by rewrite /mid /d; field.
have minus : mid + -d = t by rewrite /mid; ring.
have hp : mid + d \in time_interval by rewrite plus.
have hn : mid + -d \in time_interval by rewrite minus.
have ep := quad mid d hm hp.
have en := quad mid (-d) hm hn.
rewrite taylor_quadratic plus (ger0_norm d0) in ep.
rewrite taylor_quadratic minus normrN (ger0_norm d0) in en.
have midpoint : `|x (t + h) - (x t + h * f mid (x mid))| <= M_x3 * h ^+ 3.
  rewrite -(@x_ode mid hm).
  move/ler_normlP: ep => [ep1 ep2].
  move/ler_normlP: en => [en1 en2].
  have m0 := le_trans (normr_ge0 _) (@x3_bound mid hm).
  have pos := mulr_ge0 m0 (exprn_ge0 3 (ltW hpos)).
  rewrite ler_norml; apply/andP; split; rewrite /d in ep1 ep2 en1 en2; nra.
have lin := @solution_taylor x 1 t d M_x2
  (fun k hk => @x_derivable k (leq_trans hk (leqnSn 1))) x2_bound ht hm.
rewrite taylor_linear (@x_ode t ht) (ger0_norm d0) in lin.
pose v := f t (x t).
pose A := slope_derivative t (x t).
have pred : `|x mid - (x t + d * v)| <= M_x2 * d ^+ 2.
  by rewrite mulrC in lin.
have L0 := L_f_ge0.
have slope_mid : `|f mid (x mid) - (v + d * A)| <=
    (L_f * M_x2 + stage_constant) * d ^+ 2.
  have b := le_trans (f_lipschitz mid (x mid) (x t + d * v)) (ler_wpM2l L0 pred).
  have s := rk2_stage_remainder t (x t) d.
  have tri := ler_distD (f mid (x t + d * v)) (f mid (x mid)) (v + d * A).
  have bs : `|f mid (x t + d * v) - (v + d * A)| <= stage_constant * d ^+ 2 := s.
  nra.
have slope_rk : `|rk2_slope h t (x t) - (v + d * A)| <=
    `|beta| * (stage_constant * (p * h) ^+ 2) := rk2_slope_remainder t (x t) h.
have slope := ler_distD (v + d * A) (rk2_slope h t (x t)) (f mid (x mid)).
rewrite [`|v + d * A - f mid (x mid)|]distrC in slope.
have hs := ler_wpM2l (ltW hpos) (le_trans slope (lerD slope_rk slope_mid)).
apply: le_trans (ler_distD (x t + h * f mid (x mid)) _ _) _.
rewrite /rk2_step.
rewrite opprD addrACA subrr add0r -mulrBr normrM (ger0_norm (ltW hpos)).
rewrite distrC in midpoint.
rewrite /d in hs.
rewrite /local_constant; nra.
Qed.

Let stability_constant :=
  `|alpha| * L_f + `|beta| * L_f * (1 + `|q| * T * L_f).

Local Lemma rk2_step_stable t h x1 x2 : 0 <= h -> h <= T ->
  `|rk2_step h t x1 - rk2_step h t x2| <=
    (1 + h * stability_constant) * `|x1 - x2|.
Proof.
move=> h0 hT.
pose k1 x1 := f t x1.
pose k2 x1 := f (t + p * h) (x1 + q * h * k1 x1).
pose dist := `|x1 - x2|.
have dist0 : 0 <= dist := normr_ge0 _.
have b1 : `|k1 x1 - k1 x2| <= L_f * dist := f_lipschitz t x1 x2.
have b2 : `|k2 x1 - k2 x2| <= L_f * ((1 + `|q| * T * L_f) * dist).
  apply: le_trans (f_lipschitz _ _ _) (ler_wpM2l L_f_ge0 _).
  have diff : x1 + q * h * k1 x1 - (x2 + q * h * k1 x2) =
               (x1 - x2) + (q * h) * (k1 x1 - k1 x2) by ring.
  rewrite diff.
  apply: le_trans (ler_normD _ _) _.
  rewrite !normrM (ger0_norm h0) -/dist.
  have b := ler_wpM2l (mulr_ge0 (normr_ge0 q) h0) b1.
  have c := ler_wpM2r (mulr_ge0 L_f_ge0 dist0) (ler_wpM2l (normr_ge0 q) hT).
  by nra.
have slopes : `|alpha * (k1 x1 - k1 x2) + beta * (k2 x1 - k2 x2)| <=
    stability_constant * dist.
  apply: le_trans (ler_normD _ _) _.
  rewrite !normrM /stability_constant.
  have := lerD (ler_wpM2l (normr_ge0 alpha) b1) (ler_wpM2l (normr_ge0 beta) b2).
  by nra.
have -> : rk2_step h t x1 - rk2_step h t x2 =
    (x1 - x2) + h * (alpha * (k1 x1 - k1 x2) + beta * (k2 x1 - k2 x2)).
  rewrite /rk2_step /rk2_slope /k1 /k2; ring.
apply: le_trans (ler_normD _ _) _.
rewrite normrM (ger0_norm h0) -/dist.
have := ler_wpM2l h0 slopes.
by nra.
Qed.

Lemma rk2_global_error :
  exists2 C : R, 0 <= C & forall (h : R) (n : nat),
    0 < h -> n%:R * h <= T ->
    `|rk2 h n - x (n%:R * h)| <= C * h ^+ 2.
Proof.
pose K := `|local_constant|.
pose L := 1 + `|stability_constant|.
have K0 : 0 <= K := normr_ge0 _.
have L1 : 1 <= L by rewrite /L; have := normr_ge0 stability_constant; lra.
have L0 : 0 <= L by lra.
exists (K * expR (L * T)); first exact: mulr_ge0 K0 (expR_ge0 _).
move=> h n hpos.
pose time (i : nat) : R := i%:R * h.
pose err i := `|rk2 h i - x (time i)|.
have time0 i : 0 <= time i := mulr_ge0 (ler0n R i) (ltW hpos).
have timeS i : time i.+1 = time i + h by rewrite /time -nat1r; ring.
(* Adding B absorbs the local defect into a multiplicative recurrence. *)
pose B := K * h ^+ 2.
have B0 : 0 <= B := mulr_ge0 K0 (sqr_ge0 h).
have bound i : time i <= T -> err i + B <= B * expR (L * time i).
  elim: i => [|i ih] hi.
  - rewrite /err /time mul0r /= x_initial subrr normr0 add0r mulr0 expR0 mulr1.
    exact: lexx.
  - rewrite timeS in hi.
    have it : time i <= T by lra.
    have hT : h <= T by have := time0 i; lra.
    have local := rk2_local_error (time0 i) hpos hi.
    have stable := rk2_step_stable (time i) (rk2 h i) (x (time i)) (ltW hpos) hT.
    have rec : err i.+1 <= (1 + h * stability_constant) * err i + local_constant * h ^+ 3.
      rewrite /err timeS.
      exact: le_trans (ler_distD (rk2_step h (time i) (x (time i))) _ _) (lerD stable local).
    have e0 : 0 <= err i := normr_ge0 _.
    have v := ler_wpM2r (mulr_ge0 (ltW hpos) e0) (ler_norm stability_constant).
    have k := ler_wpM2r (exprn_ge0 3 (ltW hpos)) (ler_norm local_constant).
    have extra := ler_wpM2r (mulr_ge0 (ltW hpos) B0) L1.
    have step : err i.+1 + B <= (1 + L * h) * (err i + B).
      rewrite /L /B /K in v k extra *; nra.
    apply: le_trans step _.
    have factor0 : 0 <= 1 + L * h by have := mulr_ge0 L0 (ltW hpos); lra.
    have b := ler_wpM2l factor0 (ih it).
    have eg := ler_wpM2r (mulr_ge0 B0 (expR_ge0 (L * time i))) (expR_ge1Dx (L * h)).
    rewrite timeS [L * (_ + _)]mulrDr expRD.
    apply: le_trans (le_trans b eg) _.
    by rewrite mulrC -mulrA.
move=> tn.
have bn := bound n tn.
have eT : expR (L * time n) <= expR (L * T) by rewrite ler_expR; apply: ler_wpM2l.
have bT := ler_wpM2l B0 eT.
change (is_true (err n <= K * expR (L * T) * h ^+ 2)).
rewrite /B in bn B0 bT; nra.
Qed.

End ErrorAnalysis.
End RK.
