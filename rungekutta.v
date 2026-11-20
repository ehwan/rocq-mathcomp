From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets reals.
From mathcomp Require Import normedtype derive sequences exp.

Require Import taylor_poly taylor_remainder.
Require sequence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.
From mathcomp Require Import zify.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

HB.lock Definition my_derive1n := @derive1n.
Canonical locked_derive1n := Unlockable my_derive1n.unlock.

Section RK.

Context (R : realType).

Record rk2_coefficients := {
  rk2_alpha : R;
  rk2_beta : R;
  rk2_p : R;
  rk2_q : R;
  rk2_weights_sum : rk2_alpha + rk2_beta = 1;
  rk2_order_t : rk2_beta * rk2_p = 1 / 2;
  rk2_order_x : rk2_beta * rk2_q = 1 / 2
}.

Context (coeffs : rk2_coefficients).
Local Abbreviation alpha := (rk2_alpha coeffs).
Local Abbreviation beta := (rk2_beta coeffs).
Local Abbreviation p := (rk2_p coeffs).
Local Abbreviation q := (rk2_q coeffs).

Context (f : R -> R -> R) (x0 : R).

Section Method.
Context (h : R). (* dt *)

Let t_n (n : nat) := n%:R * h.

Definition rk2_slope (t x1 : R) : R :=
  let k1 := f t x1 in
  let k2 := f (t + p * h) (x1 + q * h * k1) in
  alpha * k1 + beta * k2.

Definition rk2_step (t x1 : R) : R := x1 + h * rk2_slope t x1.

(* X_n *)
Fixpoint rk2 (n : nat) : R :=
  match n with
  | O => x0
  | S m => rk2_step (t_n m) (rk2 m)
  end.

End Method.

Section ErrorAnalysis.

Context (x : R -> R) (T : R).
Context (T_pos : 0 < T) (x_initial : x 0 = x0).

(* MathComp differentiates a total function; the solution hypotheses and
   estimates concern its restriction to the physical time interval. *)
Local Abbreviation time_interval := (`[0, T]%R). (* domain for x(t) *)
Let ft (t x1 : R) := (fun s => f s x1)^`(1) t.
Let fx (t x1 : R) := (f t)^`(1) x1.

Definition Phi (h t x1 : R) :=
  f t x1 + h / 2 * (ft t x1 + f t x1 * fx t x1).


Context (x_ode : {in time_interval, forall t : R, x^`() t = f t (x t)}).
Context (f_x_domain: interval R).
Context (f_t_domain: interval R).
Context (x_derivable : forall k : nat, (k <= 2)%N ->
  {in time_interval, forall t : R, derivable x^`(k) t 1}).
Context (f_derivable_in_t : forall (x1 : R) (k : nat), (k <= 1)%N ->
  forall t : R, derivable (fun s => f s x1)^`(k) t 1).
Context (f_derivable_in_x : forall (t : R) (k : nat), (k <= 1)%N ->
  forall x1 : R, derivable (my_derive1n k (f t)) x1 1).
Context (ft_derivable_in_x : forall t x1 : R, derivable (ft t) x1 1).

Let ftt (t x1 : R) := (fun s => f s x1)^`(2) t.
Let ftx (t x1 : R) := (ft t)^`(1) x1.
Let fxx (t x1 : R) := (f t)^`(2) x1.

(* The stage points may lie outside the solution interval. *)
Context (M_f M_tt M_tx M_xx : R).
Context (f_bound : {in f_t_domain, forall t:R, {in f_x_domain, forall x1:R, `|f t x1| <= M_f}}).
Context (ftt_bound : {in f_t_domain, forall t:R, {in f_x_domain, forall x1:R, `|ftt t x1| <= M_tt}}).
Context (ftx_bound : {in f_t_domain, forall t:R, {in f_x_domain, forall x1:R, `|ftx t x1| <= M_tx}}).
Context (fxx_bound : {in f_t_domain, forall t:R, {in f_x_domain, forall x1:R, `|fxx t x1| <= M_xx}}).
(* Context (fxx_bound : forall t x1, `|fxx t x1| <= M_xx). *)

(* use f *)
Context (M_3 : R).
Context (x3_bound : {in time_interval, forall t : R, `|x^`(3) t| <= M_3}).
(* 
x'' = f_t + f*fx

x''' = f_tt + f_t*f_x + f*f_tx

Let M_3 := M_tt + M *)

(* Derived bounds used in the RK2 error estimates. *)
Let M_x := 2 * M_f + M_xx.
Let M_x2 := `|x^`(2) 0| + M_3 * T.
Let stage_constant := M_tt + M_xx * M_f ^+ 2 + M_tx * M_f.
Let Phi_constant := M_x + T / 2 * (M_tx + M_x ^+ 2 + M_f * M_xx).
Let exact_constant := M_3 + (M_x * M_x2 + stage_constant) / 4.

(* Taylor expansion at s + 1 bounds the first derivative on the real line. *)
Local Lemma fx_bound (t x1 : R) : t \in f_t_domain -> x1 \in f_x_domain -> 
    `|fx t x1| <= M_x.
Proof.
Admitted.
(* move=> t_in x_in.

have rem : `|f t (x1 + 1) - taylor_sum (f t) 1 x1 (x1 + 1)| <= M_xx * `|x1 + 1 - x1| ^+ 2.
apply: taylor_expansion.
- move=> k kge1 x2 x2inrange.
  apply: f_derivable_in_x.
  exact: kge1.
- move=> x2 x2range.
  apply: fxx_bound.
  exact: t_in.
  exact: x_in.
  (fun k hk s _ => f_derivable_in_x (t := t) (x1 := s) hk)
  (fun s _ => fxx_bound t s).
rewrite taylor_linear mulr1 addrAC subrr add0r normr1 expr1n mulr1 in rem.
move/ler_normlP: rem => [rem_lo rem_hi].
have /ler_normlP [x_lo x_hi] := f_bound t x1.
have /ler_normlP [next_lo next_hi] := f_bound t (x1 + 1).
rewrite /fx /M_x.
apply/ler_normlP.
by split; lra.
Qed. *)

Local Lemma segment_subset_interval (I : interval R) (a b : R) :
  a \in I -> b \in I -> {subset `[minr a b, maxr a b]%R <= I}.
Proof.
case: I => l u.
rewrite !itv_boundlr => /andP [la au] /andP [lb bu].
by case: (leP a b) => _; apply: subset_itv.
Qed.

Local Lemma lipschitz_of_derivative_bound_on_interval (g : R -> R) (M : R)
    (I : interval R) :
  {in I, forall s : R, derivable g s 1} ->
  {in I, forall s : R, `|g^`(1) s| <= M} ->
  {in I &, forall x1 x2 : R, `|g x1 - g x2| <= M * `|x1 - x2|}.
Proof.
move=> dg bg x1 x2 h1 h2.
have dg0 k : (k <= 0)%N -> {in I, forall s : R, derivable g^`(k) s 1}.
- case: k => [|k] hk; first exact: dg.
  by [].
have inside := segment_subset_interval h2 h1.
have rem := taylor_expansion (f := g) (n := 0) (a := x2) (x := x1)
  (fun k hk s hs => dg0 k hk s (inside s hs)) (fun s hs => bg s (inside s hs)).
by rewrite taylor_sum0 expr1 in rem.
Qed.

Local Lemma lipschitz_of_derivative_bound (g : R -> R) (M x1 x2 : R) :
  (forall s : R, derivable g s 1) ->
  (forall s : R, `|g^`(1) s| <= M) ->
  `|g x1 - g x2| <= M * `|x1 - x2|.
Proof.
move=> dg bg.
by apply: (lipschitz_of_derivative_bound_on_interval (I := `]-oo, +oo[%R)).
Qed.

Local Lemma x2_bound : {in time_interval, forall t : R, `|x^`(2) t| <= M_x2}.
Proof.
move=> t ht.
have /andP [t0 tT] : (0 <= t) && (t <= T) by move: ht; rewrite in_itv /=.
have h0 : 0 \in time_interval by rewrite in_itv /= lexx (le_trans t0 tT).
have diff := lipschitz_of_derivative_bound_on_interval
  (x_derivable (leqnn 2)) x3_bound ht h0.
rewrite subr0 (ger0_norm t0) in diff.
have M_3_ge0 := le_trans (normr_ge0 _) (x3_bound h0).
have tri := ler_normD (x^`(2) t - x^`(2) 0) (x^`(2) 0).
rewrite subrK in tri.
rewrite /M_x2 addrC.
exact: le_trans tri (lerD (le_trans diff (ler_wpM2l M_3_ge0 tT)) (lexx _)).
Qed.

(* Lipschitz bounds in x for fixed t. *)
Local Lemma f_lipschitz (t x1 x2 : R) :
  x1 \in f_x_domain -> x2 \in f_x_domain ->
  `|f t x1 - f t x2| <= M_x * `|x1 - x2|.
Proof.
move=> x1domain x2domain.
apply: (lipschitz_of_derivative_bound_on_interval (I:= f_x_domain)).
- move=> s sdomain.
  apply: (@f_derivable_in_x _).

exact: (f_derivable_in_x t (leq0n 1)).
- move=> s.
  apply: fx_bound.
- exact: fx_bound t.
Qed.

Local Lemma ft_lipschitz (t x1 x2 : R) :
  `|ft t x1 - ft t x2| <= M_tx * `|x1 - x2|.
Proof.
apply: lipschitz_of_derivative_bound.
- exact: ft_derivable_in_x t.
- exact: ftx_bound t.
Qed.

Local Lemma fx_lipschitz (t x1 x2 : R) :
  `|fx t x1 - fx t x2| <= M_xx * `|x1 - x2|.
Proof.
apply: lipschitz_of_derivative_bound.
- exact: (f_derivable_in_x (t := t) (leqnn 1)).
- exact: fxx_bound t.
Qed.

Lemma Phi_lipschitz (h t x1 x2 : R) : 0 <= h -> h <= T ->
  `|Phi h t x1 - Phi h t x2| <= Phi_constant * `|x1 - x2|.
Proof.
move=> h0 hT.
pose dist := `|x1 - x2|.
have bf := f_lipschitz t x1 x2.
have bt := ft_lipschitz t x1 x2.
have bx := fx_lipschitz t x1 x2.
have bprod1 := ler_pM (normr_ge0 _) (normr_ge0 _) (fx_bound t x1) bf.
have bprod2 := ler_pM (normr_ge0 _) (normr_ge0 _) (f_bound t x2) bx.
have bd : `|ft t x1 + f t x1 * fx t x1 - (ft t x2 + f t x2 * fx t x2)| <=
    (M_tx + M_x ^+ 2 + M_f * M_xx) * dist.
- have -> : ft t x1 + f t x1 * fx t x1 - (ft t x2 + f t x2 * fx t x2) =
      (ft t x1 - ft t x2) + fx t x1 * (f t x1 - f t x2) +
      f t x2 * (fx t x1 - fx t x2) by ring.
  apply: le_trans (ler_normD _ _) _.
  apply: le_trans (lerD (ler_normD _ _) (lexx _)) _.
  rewrite !normrM /dist.
  move: (lerD (lerD bt bprod1) bprod2).
  by nra.
have half0 : 0 <= h / 2 by lra.
have halfT : h / 2 <= T / 2 by lra.
have scale := ler_pM half0 (normr_ge0 _) halfT bd.
rewrite /Phi.
rewrite opprD addrACA -mulrBr.
apply: le_trans (ler_normD _ _) _.
rewrite normrM (ger0_norm half0).
rewrite /dist in scale.
rewrite /Phi_constant.
by nra.
Qed.

(* Expand each coordinate separately, keeping the first slope fixed. *)
Lemma rk2_stage_remainder (t x1 dt : R) :
  `|f (t + dt) (x1 + dt * f t x1) -
    (f t x1 + dt * (ft t x1 + f t x1 * fx t x1))| <= stage_constant * dt ^+ 2.
Proof.
pose v := f t x1.
pose dx := dt * v.
pose w := x1 + dx.
have et := taylor_expansion (f := fun s => f s w) (n := 1) (a := t) (x := t + dt)
  (fun k hk s _ => f_derivable_in_t (x1 := w) (t := s) hk)
  (fun s _ => ftt_bound s w).
have ex := taylor_expansion (f := f t) (n := 1) (a := x1) (x := x1 + dx)
  (fun k hk s _ => f_derivable_in_x (t := t) (x1 := s) hk)
  (fun s _ => fxx_bound t s).
rewrite taylor_linear addrAC subrr add0r in et.
rewrite taylor_linear addrAC subrr add0r in ex.
have em := ft_lipschitz t w x1.
have dw : w - x1 = dx by rewrite /w; ring.
rewrite dw /dx normrM in em.
have bv : `|v| <= M_f := f_bound t x1.
have hxx := le_trans (normr_ge0 _) (fxx_bound t x1).
have hL := le_trans (normr_ge0 _) (ftx_bound t x1).
have bv2 : `|v| ^+ 2 <= M_f ^+ 2.
- move: (normr_ge0 v).
  by nra.
have ex' : `|f t w - (v + fx t x1 * dx)| <=
    M_xx * M_f ^+ 2 * dt ^+ 2.
- apply: le_trans ex _.
  rewrite /dx normrM exprMn !(real_normK (num_real _)).
  have hs := ler_wpM2l hxx bv2.
  rewrite (real_normK (num_real _)) in hs.
  move: (ler_wpM2r (sqr_ge0 dt) hs).
  by nra.
have em' : `|(ft t w - ft t x1) * dt| <= M_tx * M_f * dt ^+ 2.
- rewrite normrM.
  apply: le_trans (ler_wpM2r (normr_ge0 dt) em) _.
  have h := ler_wpM2l hL bv.
  move: (ler_wpM2r (sqr_ge0 `|dt|) h).
  rewrite -(real_normK (num_real dt)).
  by nra.
rewrite (real_normK (num_real _)) in et.
have /ler_normlP [t_taylor_lo t_taylor_hi] :
    `|f (t + dt) w - (f t w + ft t w * dt)| <= M_tt * dt ^+ 2 := et.
move/ler_normlP: ex' => [x_taylor_lo x_taylor_hi].
move/ler_normlP: em' => [mixed_lo mixed_hi].
rewrite -/v -/dx -/w.
rewrite /dx in x_taylor_lo x_taylor_hi.
rewrite /stage_constant.
apply/ler_normlP.
by split; nra.
Qed.

(* The order conditions match the linear term in the weighted stage slopes. *)
Lemma rk2_slope_remainder (t x1 h : R) :
  `|rk2_slope h t x1 - Phi h t x1| <=
    `|beta| * (stage_constant * (p * h) ^+ 2).
Proof.
have bp0 : beta != 0.
- apply/eqP.
  move: (rk2_order_t coeffs).
  by nra.
have pq : p = q.
- apply: (mulfI bp0).
  by rewrite rk2_order_t rk2_order_x.
pose v := f t x1.
pose A := ft t x1 + v * fx t x1.
pose k2 := f (t + p * h) (x1 + p * h * v).
have stage : `|k2 - (v + p * h * A)| <= stage_constant * (p * h) ^+ 2 :=
  rk2_stage_remainder t x1 (p * h).
rewrite /Phi /rk2_slope.
rewrite -pq -/v -/k2 -/A.
have -> : alpha * v + beta * k2 - (v + h / 2 * A) =
    beta * (k2 - (v + p * h * A)).
- have -> : alpha = 1 - beta by move: (rk2_weights_sum coeffs); lra.
  have -> : h / 2 * A = beta * p * h * A by rewrite rk2_order_t; ring.
  by ring.
rewrite normrM.
exact: (ler_wpM2l (normr_ge0 beta) stage).
Qed.

(* Compare the numerical slope to x' at the midpoint, where the ODE holds. *)
Lemma exact_Phi_remainder (t h : R) :
  0 <= t -> 0 < h -> t + h <= T ->
  `|x (t + h) - (x t + h * Phi h t (x t))| <= exact_constant * h ^+ 3.
Proof.
move=> t0 hpos endT.
pose dt := h / 2.
pose mid := t + dt.
have dt0 : 0 <= dt by rewrite /dt; lra.
have ht : t \in time_interval.
- rewrite in_itv /=.
  apply/andP.
  by split; lra.
have hm : mid \in time_interval.
- rewrite /mid /dt in_itv /=.
  apply/andP.
  by split; lra.
have he : t + h \in time_interval.
- rewrite in_itv /=.
  apply/andP.
  by split; lra.
have quad (d : R) (hb : mid + d \in time_interval) :=
  let inside := segment_subset_interval hm hb in
  taylor_expansion (f := x) (n := 2) (a := mid) (x := mid + d)
    (fun k hk s hs => x_derivable hk (inside s hs))
    (fun s hs => x3_bound (inside s hs)).
have plus : mid + dt = t + h by rewrite /mid /dt; field.
have minus : mid + -dt = t by rewrite /mid; ring.
have hp : mid + dt \in time_interval by rewrite plus.
have hn : mid + -dt \in time_interval by rewrite minus.
have ep := quad dt hp.
have en := quad (-dt) hn.
rewrite [mid + dt - mid]addrAC subrr add0r taylor_quadratic plus in ep.
rewrite (ger0_norm dt0) in ep.
rewrite [mid + -dt - mid]addrAC subrr add0r taylor_quadratic minus in en.
rewrite normrN (ger0_norm dt0) in en.
have midpoint : `|x (t + h) - (x t + h * f mid (x mid))| <= M_3 * h ^+ 3.
- rewrite -(x_ode hm).
  move/ler_normlP: ep => [ep1 ep2].
  move/ler_normlP: en => [en1 en2].
  have m0 := le_trans (normr_ge0 _) (x3_bound hm).
  rewrite /dt in ep1 ep2 en1 en2.
  Admitted.
  (* apply/ler_normlP.
  split.
  nra.
  by split; nra.
have inside := segment_subset_interval ht hm.
have lin := taylor_expansion (f := x) (n := 1) (a := t) (x := t + dt)
  (fun k hk s hs => x_derivable (leq_trans hk (leqnSn 1)) (inside s hs))
  (fun s hs => x2_bound (inside s hs)).
rewrite taylor_linear (x_ode ht) addrAC subrr add0r in lin.
rewrite (ger0_norm dt0) in lin.
pose v := f t (x t).
pose dx := dt * v.
pose A := ft t (x t) + v * fx t (x t).
have pred : `|x mid - (x t + dx)| <= M_x2 * dt ^+ 2 by rewrite mulrC in lin.
have slope_mid : `|f mid (x mid) - (v + dt * A)| <=
    (M_x * M_x2 + stage_constant) * dt ^+ 2.
- have M_x_ge0 := le_trans (normr_ge0 _) (fx_bound t (x t)).
  have b := le_trans (f_lipschitz mid (x mid) (x t + dx))
                     (ler_wpM2l M_x_ge0 pred).
  have stage : `|f mid (x t + dx) - (v + dt * A)| <=
      stage_constant * dt ^+ 2 :=
    rk2_stage_remainder t (x t) dt.
  move/ler_normlP: b => [slope_diff_lo slope_diff_hi].
  move/ler_normlP: stage => [stage_lo stage_hi].
  apply/ler_normlP.
  by split; lra.
move/ler_normlP: slope_mid => [mid_lo mid_hi].
move/ler_normlP: midpoint => [step_lo step_hi].
rewrite /dt in mid_lo mid_hi.
rewrite /Phi -/v -/A.
rewrite /exact_constant.
apply/ler_normlP.
by split; nra.
Qed. *)

Let local_constant := exact_constant + `|beta| * stage_constant * p ^+ 2.

(* Compare Phi at the approximation x1 and the exact value x(t). *)
Lemma rk2_error_step (t h x1 : R) : 0 <= t -> 0 < h -> t + h <= T ->
  `|rk2_step h t x1 - x (t + h)| <=
    (1 + h * Phi_constant) * `|x1 - x t| + local_constant * h ^+ 3.
Proof.
move=> t0 hpos endT.
have hT : h <= T by lra.
have /ler_normlP [rk_lo rk_hi] := rk2_slope_remainder t x1 h.
have /ler_normlP [phi_lo phi_hi] := Phi_lipschitz t x1 (x t) (ltW hpos) hT.
have /ler_normlP [exact_lo exact_hi] := exact_Phi_remainder t0 hpos endT.
have /ler_normlP [x_error_lo x_error_hi] := lexx `|x1 - x t|.
rewrite /rk2_step /local_constant.
apply/ler_normlP.
by split; nra.
Qed.

Lemma rk2_local_error (t h : R) :
  0 <= t -> 0 < h -> t + h <= T ->
  `|rk2_step h t (x t) - x (t + h)| <= local_constant * h ^+ 3.
Proof.
move=> t0 hpos endT.
move: (rk2_error_step (x t) t0 hpos endT).
rewrite subrr normr0.
by rewrite mulr0 add0r.
Qed.

Lemma rk2_global_error :
  exists2 C : R, 0 <= C & forall (h : R) (n : nat),
    0 < h -> n%:R * h <= T ->
    `|rk2 h n - x (n%:R * h)| <= C * h ^+ 2.
Proof.
pose K := `|local_constant|.
pose L := 1 + `|Phi_constant|.
have K0 : 0 <= K := normr_ge0 _.
have Lpos : 0 < L.
- rewrite /L.
  move: (normr_ge0 Phi_constant).
  by lra.
have exp1 := expR_ge1Dx (L * T).
have LT0 := mulr_ge0 (ltW Lpos) (ltW T_pos).
exists ((K / L) * (expR (L * T) - 1)).
- apply: mulr_ge0 (divr_ge0 K0 (ltW Lpos)) _.
  by lra.
move=> h n hpos.
pose time (i : nat) : R := i%:R * h.
pose E (i : nat) : R := `|rk2 h i - x (time i)|.
apply: (sequence.discrete_gronwall_order2 (E := E) (T := T) hpos Lpos K0).
- rewrite /E /time mul0r /=.
  by rewrite x_initial subrr normr0.
move=> i ti.
have timeS : time i.+1 = time i + h by rewrite /time -nat1r; ring.
rewrite -/(time i.+1) timeS in ti.
have t0 : 0 <= time i := mulr_ge0 (ler0n _ i) (ltW hpos).
have rec : E i.+1 <= (1 + h * Phi_constant) * E i + local_constant * h ^+ 3.
- rewrite /E timeS.
  exact: rk2_error_step (rk2 h i) t0 hpos ti.
have e0 : 0 <= E i := normr_ge0 _.
have s := ler_wpM2r (mulr_ge0 (ltW hpos) e0) (ler_norm Phi_constant).
have k := ler_wpM2r (exprn_ge0 3 (ltW hpos)) (ler_norm local_constant).
rewrite /L /K.
by nra.
Qed.

End ErrorAnalysis.
End RK.
