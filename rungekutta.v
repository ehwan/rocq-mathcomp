From mathcomp Require Import boot order ssralg ssrnum interval.
From mathcomp Require Import classical_sets functions reals filter.
From mathcomp Require Import topology normedtype derive sequences exp.

Require Export ode.
Require Import taylor_poly taylor_expansion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

From mathcomp Require Import ring_tactic field_tactic arithmetic_tactic.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RK2.

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

Section Method.
Context (f : R -> R -> R) (x_0 : R).

Local Definition K_1 (t_n X_n : R) : R := f t_n X_n.

Local Definition K_2 (h t_n X_n : R) : R :=
  f (t_n + p * h) (X_n + q * h * K_1 t_n X_n).

Local Definition t_n (h : R) (n : nat) : R := n%:R * h.

Local Lemma t_nS (h : R) (n : nat) : t_n h n.+1 = t_n h n + h.
Proof.
rewrite /t_n -nat1r.
by ring.
Qed.

Local Definition rk2_step (h t_n X_n : R) : R :=
  X_n + h * (alpha * K_1 t_n X_n + beta * K_2 h t_n X_n).

Fixpoint X_n (h : R) (n : nat) : R :=
  match n with
  | O => x_0
  | S m => rk2_step h (t_n h m) (X_n h m)
  end.

End Method.

Context (problem : ode R) (T : R) (T_pos : 0 < T).
Local Abbreviation x_0 := (ode_x_0 problem).
Local Abbreviation f := (ode_f problem).
Local Abbreviation f_domain_t := (ode_f_domain_t problem).
Local Abbreviation f_domain_x := (ode_f_domain_x problem).
Local Abbreviation integration_interval := (`[0, T]%R).
Context (integration_interval_in_ode_interval :
  {subset integration_interval <= ode_interval problem}).

Definition partial_t (g : R -> R -> R) (t y : R) : R :=
  (fun s => g s y)^`(1) t.
Definition partial_x (g : R -> R -> R) (t y : R) : R :=
  (g t)^`(1) y.

Definition has_partials (g_domain_t g_domain_x : interval R) (g gt gx : R -> R -> R) : Prop :=
  {in g_domain_t, forall t : R, {in g_domain_x, forall y : R,
    is_diff (t, y) (fun z : R * R => g z.1 z.2)
      (fun dz : R * R => gt t y * dz.1 + gx t y * dz.2)}}.

Definition bounded_on_rectangle (g_domain_t g_domain_x : interval R)
    (g : R -> R -> R) (M : R) : Prop :=
  {in g_domain_t, forall t : R, {in g_domain_x, forall y : R, `|g t y| <= M}}.

Local Abbreviation f_t := (partial_t f).
Local Abbreviation f_x := (partial_x f).
Local Abbreviation f_tt := (partial_t f_t).
Local Abbreviation f_tx := (partial_x f_t).
Local Abbreviation f_xx := (partial_x f_x).

Record rk2_regularity := {
  rk2_f_diff : has_partials f_domain_t f_domain_x f f_t f_x;
  (* The two mixed partials agree on the rectangle. *)
  rk2_f_t_diff : has_partials f_domain_t f_domain_x f_t f_tt f_tx;
  rk2_f_x_diff : has_partials f_domain_t f_domain_x f_x f_tx f_xx;

  rk2_M_f : R;
  rk2_M_x : R;
  rk2_M_tt : R;
  rk2_M_tx : R;
  rk2_M_xx : R;
  rk2_f_bound : bounded_on_rectangle f_domain_t f_domain_x f rk2_M_f;
  rk2_f_x_bound : bounded_on_rectangle f_domain_t f_domain_x f_x rk2_M_x;
  rk2_f_tt_bound : bounded_on_rectangle f_domain_t f_domain_x f_tt rk2_M_tt;
  rk2_f_tx_bound : bounded_on_rectangle f_domain_t f_domain_x f_tx rk2_M_tx;
  rk2_f_xx_bound : bounded_on_rectangle f_domain_t f_domain_x f_xx rk2_M_xx
}.

Context (regularity : rk2_regularity).
Local Abbreviation M_f := (rk2_M_f regularity).
Local Abbreviation M_x := (rk2_M_x regularity).
Local Abbreviation M_tt := (rk2_M_tt regularity).
Local Abbreviation M_tx := (rk2_M_tx regularity).
Local Abbreviation M_xx := (rk2_M_xx regularity).

Local Lemma integration_interval_in_f_domain_t : {subset integration_interval <= f_domain_t}.
Proof.
move=> t ht.
apply: ode_interval_in_domain_t.
apply: integration_interval_in_ode_interval.
exact: ht.
Qed.

Local Definition K_2_in_domain (h t_n X_n : R) : Prop :=
  t_n + p * h \in f_domain_t /\ X_n + q * h * K_1 f t_n X_n \in f_domain_x.

Local Definition Phi (h t x1 : R) : R :=
  f t x1 + h / 2 * (f_t t x1 + f t x1 * f_x t x1).

Local Lemma norm_bound_ge0 (a A : R) : `|a| <= A -> 0 <= A.
Proof.
move=> bound.
have a0 : 0 <= `|a|.
- exact: normr_ge0.
by lra.
Qed.

Local Lemma norm_sum_bound (a b A B : R) :
  `|a| <= A -> `|b| <= B -> `|a + b| <= A + B.
Proof.
move=> ha hb.
apply: le_trans.
- exact: ler_normD.
- apply: lerD.
  + exact: ha.
  + exact: hb.
Qed.

Local Lemma norm_product_bound (a b A B : R) :
  `|a| <= A -> `|b| <= B -> `|a * b| <= A * B.
Proof.
move=> ha hb.
rewrite normrM.
apply: ler_pM.
- exact: normr_ge0.
- exact: normr_ge0.
- exact: ha.
- exact: hb.
Qed.

(* The equality recurrence has general term (r ^+ n - 1) * B,
   where r = 1 + h * L and B = (K / L) * h ^+ 2. *)
Local Lemma E_n_geometric_bound (E : nat -> R) (h L K : R) (n : nat) :
  0 < h -> 0 < L -> E 0%N = 0 ->
  (forall i : nat, (i < n)%N -> E i.+1 <= (1 + h * L) * E i + K * h ^+ 3) ->
  E n <= ((1 + h * L) ^+ n - 1) * ((K / L) * h ^+ 2).
Proof.
move=> hpos Lpos initial.
pose r := 1 + h * L.
pose B := (K / L) * h ^+ 2.
have r0 : 0 <= r.
- rewrite /r.
  by nra.
have shift : (r - 1) * B = K * h ^+ 3.
- rewrite /r /B.
  have Lnz : L != 0.
  + by lra.
  by field.
rewrite -/r -/B.
elim: n => [|n IH] recurrence.
- rewrite initial.
  by rewrite expr0 subrr mul0r.
- have prev : E n <= (r ^+ n - 1) * B.
  + apply: IH.
    move=> i hin.
    apply: recurrence.
    apply: leqW.
    exact: hin.
  have step : E n.+1 <= r * E n + K * h ^+ 3.
  + apply: recurrence.
    exact: ltnSn.
  rewrite -shift in step.
  rewrite exprS.
  by nra.
Qed.

Local Lemma geometric_exp_bound (u B : R) (n : nat) :
  0 <= u -> 0 <= B ->
  ((1 + u) ^+ n - 1) * B <= (expR (n%:R * u) - 1) * B.
Proof.
move=> u0 B0.
apply: ler_wpM2r.
- exact: B0.
- rewrite lerD2r.
  rewrite expRM_natl.
  apply: lerXn2r.
  + change (0 <= 1 + u).
    by lra.
  + exact: expR_ge0.
  + exact: expR_ge1Dx.
Qed.

Local Lemma E_n_exp_bound (E : nat -> R) (h L K : R) (n : nat) :
  0 < h -> 0 < L -> 0 <= K -> n%:R * h <= T ->
  E 0%N = 0 ->
  (forall i : nat, (i < n)%N -> E i.+1 <= (1 + h * L) * E i + K * h ^+ 3) ->
  E n <= (expR (L * T) - 1) * (K / L) * h ^+ 2.
Proof.
move=> hpos Lpos K0 endT initial recurrence.
pose B := (K / L) * h ^+ 2.
have B0 : 0 <= B.
- apply: mulr_ge0.
  + apply: divr_ge0.
    * exact: K0.
    * by lra.
  + exact: sqr_ge0.
have geom : E n <= ((1 + h * L) ^+ n - 1) * B.
- apply: E_n_geometric_bound.
  + exact: hpos.
  + exact: Lpos.
  + exact: initial.
  + exact: recurrence.
have at_n : ((1 + h * L) ^+ n - 1) * B <= (expR (n%:R * (h * L)) - 1) * B.
- apply: geometric_exp_bound.
  + by nra.
  + exact: B0.
rewrite -mulrA -/B.
apply: le_trans.
- exact: geom.
- apply: le_trans.
  + exact: at_n.
  + apply: ler_wpM2r.
    * exact: B0.
    * rewrite lerD2r ler_expR.
      rewrite mulrA [L * T]mulrC.
      by rewrite ler_pM2r //.
Qed.

Local Lemma rk2_taylor_bound (g : R -> R) (n : nat) (a y M : R)
    (I : interval R) :
  a \in I -> y \in I ->
  (forall k : nat, (k <= n)%N -> {in I, forall s : R, derivable (g^`(k)) s 1}) ->
  {in I, forall s : R, `|g^`(n.+1) s| <= M} ->
  `|g y - taylor_sum g n a y| <= M * `|y - a| ^+ n.+1.
Proof.
move=> a_in y_in dg bound.
have rem : `|g y - taylor_sum g n a y| <= M / n.+1`!%:R * `|y - a| ^+ n.+1.
- apply: taylor_expansion_bound.
  + exact: a_in.
  + exact: dg.
  + exact: y_in.
  + exact: bound.
apply: le_trans.
- exact: rem.
- apply: ler_wpM2r.
  + apply: exprn_ge0.
    exact: normr_ge0.
  + rewrite ler_pdivrMr ?ltr0n ?fact_gt0 //.
    have fact_ge1 : 1 <= n.+1`!%:R :> R.
    * by rewrite ler1n fact_gt0.
    have M_ge0 : 0 <= M.
    * apply: norm_bound_ge0.
      apply: bound.
      exact: a_in.
    by nra.
Qed.

Local Lemma lipschitz_of_derivative_bound_on_interval (g : R -> R) (M : R)
    (I : interval R) :
  {in I, forall s : R, derivable g s 1} ->
  {in I, forall s : R, `|g^`(1) s| <= M} ->
  {in I &, forall x1 x2 : R, `|g x1 - g x2| <= M * `|x1 - x2|}.
Proof.
move=> dg bg x1 x2 h1 h2.
have rem : `|g x1 - taylor_sum g 0 x2 x1| <= M * `|x1 - x2| ^+ 1.
- apply: rk2_taylor_bound.
  + exact: h2.
  + exact: h1.
  + by case=> [|k].
  + exact: bg.
by rewrite taylor_sum0 expr1 in rem.
Qed.

(* Stability of Phi in the state variable. *)
Let Phi_constant : R := M_x + T / 2 * (M_tx + M_x ^+ 2 + M_f * M_xx).

Let L : R := 1 + `|Phi_constant|.

Local Lemma L_positive : 0 < L.
Proof.
rewrite /L.
have bound : 0 <= `|Phi_constant|.
- exact: normr_ge0.
by lra.
Qed.

Section CoordinateLines.

Context (g g_t g_x : R -> R -> R) (g_diff : has_partials f_domain_t f_domain_x g g_t g_x).
Context (t y : R) (ht : t \in f_domain_t) (hy : y \in f_domain_x).

Local Lemma differentiable_of_partials :
  differentiable (fun z : R * R => g z.1 z.2) (t, y).
Proof.
have [dg _] : is_diff (t, y) (fun z : R * R => g z.1 z.2)
    (fun dz : R * R => g_t t y * dz.1 + g_x t y * dz.2).
- apply: g_diff.
  + exact: ht.
  + exact: hy.
exact: dg.
Qed.

Local Lemma derivable_in_x_of_partials : derivable (g t) y 1.
Proof.
change (derivable ((fun z : R * R => g z.1 z.2) \o (fun r : R => (t, r))) y 1).
apply: diff_derivable.
apply: differentiable_comp.
- exact: ex_diff.
- exact: differentiable_of_partials.
Qed.

Local Lemma derivable_in_t_of_partials : derivable (fun r => g r y) t 1.
Proof.
change (derivable ((fun z : R * R => g z.1 z.2) \o (fun r : R => (r, y))) t 1).
apply: diff_derivable.
apply: differentiable_comp.
- exact: ex_diff.
- exact: differentiable_of_partials.
Qed.

End CoordinateLines.

Local Lemma f_derivable_in_x (t y : R) (k : nat) :
  t \in f_domain_t -> y \in f_domain_x -> (k <= 1)%N ->
  derivable (f t)^`(k) y 1.
Proof.
move=> ht hy.
case: k => [|[|k]] // _.
- change (derivable (f t) y 1).
  apply: derivable_in_x_of_partials.
  + exact: (rk2_f_diff regularity).
  + exact: ht.
  + exact: hy.
- change (derivable (f_x t) y 1).
  apply: derivable_in_x_of_partials.
  + exact: (rk2_f_x_diff regularity).
  + exact: ht.
  + exact: hy.
Qed.

Local Lemma f_derivable_in_t (s y : R) (k : nat) :
  s \in f_domain_t -> y \in f_domain_x -> (k <= 1)%N ->
  derivable (fun r => f r y)^`(k) s 1.
Proof.
move=> hs hy.
case: k => [|[|k]] // _.
- change (derivable (fun r => f r y) s 1).
  apply: derivable_in_t_of_partials.
  + exact: (rk2_f_diff regularity).
  + exact: hs.
  + exact: hy.
- change (derivable (fun r => f_t r y) s 1).
  apply: derivable_in_t_of_partials.
  + exact: (rk2_f_t_diff regularity).
  + exact: hs.
  + exact: hy.
Qed.

Local Lemma f_lipschitz (t x1 x2 : R) :
  t \in f_domain_t -> x1 \in f_domain_x -> x2 \in f_domain_x ->
  `|f t x1 - f t x2| <= M_x * `|x1 - x2|.
Proof.
move=> ht hx hx2.
apply: lipschitz_of_derivative_bound_on_interval.
- move=> y hy.
  apply: derivable_in_x_of_partials.
  + exact: (rk2_f_diff regularity).
  + exact: ht.
  + exact: hy.
- apply: rk2_f_x_bound.
  exact: ht.
- exact: hx.
- exact: hx2.
Qed.

Local Lemma f_t_lipschitz (t x1 x2 : R) :
  t \in f_domain_t -> x1 \in f_domain_x -> x2 \in f_domain_x ->
  `|f_t t x1 - f_t t x2| <= M_tx * `|x1 - x2|.
Proof.
move=> ht hx hx2.
apply: lipschitz_of_derivative_bound_on_interval.
- move=> y hy.
  apply: derivable_in_x_of_partials.
  + exact: (rk2_f_t_diff regularity).
  + exact: ht.
  + exact: hy.
- apply: rk2_f_tx_bound.
  exact: ht.
- exact: hx.
- exact: hx2.
Qed.

Local Lemma f_x_lipschitz (t x1 x2 : R) :
  t \in f_domain_t -> x1 \in f_domain_x -> x2 \in f_domain_x ->
  `|f_x t x1 - f_x t x2| <= M_xx * `|x1 - x2|.
Proof.
move=> ht hx hx2.
apply: lipschitz_of_derivative_bound_on_interval.
- move=> y hy.
  apply: derivable_in_x_of_partials.
  + exact: (rk2_f_x_diff regularity).
  + exact: ht.
  + exact: hy.
- apply: rk2_f_xx_bound.
  exact: ht.
- exact: hx.
- exact: hx2.
Qed.

(* Derivatives of the exact solution and its Taylor remainder. *)
Let M_dft : R := M_tt + M_tx * M_f.
Let M_x2 (ft0 : R) : R := `|ft0| + M_dft * T + M_f * M_x.
Let M_3 (ft0 : R) : R := M_dft + (M_f * (M_tx + M_xx * M_f) + M_x * M_x2 ft0).

Let M_K2 : R :=
  M_tt * p ^+ 2 + M_xx * M_f ^+ 2 * q ^+ 2 + M_tx * M_f * (`|q| * `|p|).

Let K (ft0 : R) : R := `|M_3 ft0 + `|beta| * M_K2|.

(* ft0 is the time partial derivative of f at (0, x_0). *)
Definition rk2_error_radius (ft0 : R) : R :=
  (expR (L * T) - 1) * (K ft0 / L).

Local Abbreviation error_bound x C :=
  (forall (h : R) (n : nat),
    0 < h -> n%:R * h <= T ->
    (forall i : nat, (i < n)%N ->
      X_n f x_0 h i \in f_domain_x /\
      i%:R * h + p * h \in f_domain_t /\
      X_n f x_0 h i + q * h * f (i%:R * h) (X_n f x_0 h i) \in f_domain_x) ->
    `|x (n%:R * h) - X_n f x_0 h n| <= C * h ^+ 2).

Local Abbreviation ft_initial := (f_t 0 x_0).

(* Prove the estimate for any witness before applying the existence lemma. *)
Section ErrorForSolution.
Variable x : R -> R.
Hypothesis x_initial : x 0 = x_0.
Hypothesis x_ode : {in integration_interval, forall t : R, is_derive t 1 x (f t (x t))}.
Hypothesis solution_in_f_domain_x : {in integration_interval, forall t : R, x t \in f_domain_x}.
Local Definition E_n (h : R) (n : nat) : R := `|x (t_n h n) - X_n f x_0 h n|.

Local Lemma E_n_initial (h : R) : E_n h 0%N = 0.
Proof.
rewrite /E_n /t_n mul0r /=.
by rewrite x_initial subrr normr0.
Qed.

Local Notation "'along' g" := (fun s : R => g s (x s)) (at level 10).

Local Lemma derivative_along_solution (t : R) (g g_t g_x : R -> R -> R) :
  t \in integration_interval -> has_partials f_domain_t f_domain_x g g_t g_x ->
  is_derive t 1 (along g)
    (g_t t (x t) + g_x t (x t) * f t (x t)).
Proof.
move=> ht g_diff.
have [dx dxE] : is_derive t 1 x (f t (x t)).
- apply: x_ode.
  exact: ht.
have dx' : is_diff t x (fun h => h * f t (x t)).
- apply: DiffDef.
  + apply/derivable1_diffP.
    exact: dx.
  + by rewrite deriv1E // derive1E dxE.
pose curve := fun s : R => (s, x s).
pose tangent := fun h : R => (h, h * f t (x t)).
pose dg := fun dz : R * R => g_t t (x t) * dz.1 + g_x t (x t) * dz.2.
have [dcomp dcompE] : is_diff t ((fun z : R * R => g z.1 z.2) \o curve) (dg \o tangent).
- apply: is_diff_comp.
  apply: g_diff.
  + apply: integration_interval_in_f_domain_t.
    exact: ht.
  + apply: solution_in_f_domain_x.
    exact: ht.
apply: DeriveDef.
- apply: diff_derivable.
  exact: dcomp.
- rewrite deriveE // dcompE.
  rewrite /dg /tangent /=.
  by ring.
Qed.

Local Lemma f_solution_derivative (t : R) : t \in integration_interval ->
  is_derive t 1 (along f)
    (f_t t (x t) + f_x t (x t) * f t (x t)).
Proof.
move=> ht.
apply: derivative_along_solution.
- exact: ht.
- exact: (rk2_f_diff regularity).
Qed.

Local Lemma f_t_solution_derivative (t : R) : t \in integration_interval ->
  is_derive t 1 (along f_t)
    (f_tt t (x t) + f_tx t (x t) * f t (x t)).
Proof.
move=> ht.
apply: derivative_along_solution.
- exact: ht.
- exact: (rk2_f_t_diff regularity).
Qed.

Local Lemma f_x_solution_derivative (t : R) : t \in integration_interval ->
  is_derive t 1 (along f_x)
    (f_tx t (x t) + f_xx t (x t) * f t (x t)).
Proof.
move=> ht.
apply: derivative_along_solution.
- exact: ht.
- exact: (rk2_f_x_diff regularity).
Qed.

Let acceleration (t : R) : R := f_t t (x t) + f t (x t) * f_x t (x t).

Let jerk (t : R) : R :=
  (f_tt t (x t) + f_tx t (x t) * f t (x t)) +
  (f t (x t) * (f_tx t (x t) + f_xx t (x t) * f t (x t)) +
   f_x t (x t) * acceleration t).

Local Lemma acceleration_derivative (t : R) : t \in integration_interval ->
  is_derive t 1 acceleration (jerk t).
Proof.
move=> ht.
apply: is_derive_eq.
- change acceleration with
    ((along f_t) + (along f) * (along f_x))%R.
  apply: is_deriveD.
  + apply: f_t_solution_derivative.
    exact: ht.
  + apply: is_deriveM.
    * apply: f_solution_derivative.
      exact: ht.
    * apply: f_x_solution_derivative.
      exact: ht.
- by rewrite /jerk /acceleration /= [f_x t (x t) * f t (x t)]mulrC.
Qed.

Local Lemma dft_along_bound : {in integration_interval, forall t : R,
  `|f_tt t (x t) + f_tx t (x t) * f t (x t)| <= M_dft}.
Proof.
move=> t ht.
have htf : t \in f_domain_t.
- apply: integration_interval_in_f_domain_t.
  exact: ht.
have hx : x t \in f_domain_x.
- apply: solution_in_f_domain_x.
  exact: ht.
apply: norm_sum_bound.
- apply: rk2_f_tt_bound.
  + exact: htf.
  + exact: hx.
- apply: norm_product_bound.
  + apply: rk2_f_tx_bound.
    * exact: htf.
    * exact: hx.
  + apply: rk2_f_bound.
    * exact: htf.
    * exact: hx.
Qed.

Local Lemma dft_bound :
  {in integration_interval, forall t : R, `|(along f_t)^`(1) t| <= M_dft}.
Proof.
move=> t ht.
have [_ dtE] : is_derive t 1 (along f_t)
    (f_tt t (x t) + f_tx t (x t) * f t (x t)).
- apply: f_t_solution_derivative.
  exact: ht.
rewrite derive1n1 derive1E dtE.
apply: dft_along_bound.
exact: ht.
Qed.

Local Lemma acceleration_bound : {in `[0, T]%R, forall t : R, `|acceleration t| <= M_x2 ft_initial}.
Proof.
move=> t ht.
have h0 : 0 \in integration_interval.
- rewrite in_itv /= lexx /=.
  apply: ltW.
  exact: T_pos.
have /andP [t0 tT] : (0 <= t) && (t <= T).
- exact: ht.
pose ft_curve := along f_t.
have lip : {in integration_interval &, forall u v : R,
    `|ft_curve u - ft_curve v| <= M_dft * `|u - v|}.
- apply: lipschitz_of_derivative_bound_on_interval.
  + move=> s hs.
    apply: ex_derive.
    apply: f_t_solution_derivative.
    exact: hs.
  + exact: dft_bound.
have ft_change : `|ft_curve t - ft_curve 0| <= M_dft * `|t - 0|.
- apply: lip.
  + exact: ht.
  + exact: h0.
rewrite /ft_curve /= subr0 [`|t|]ger0_norm // in ft_change.
have dft0 : 0 <= M_dft.
- apply: norm_bound_ge0.
  apply: dft_bound.
  exact: ht.
have diff_norm : `|f_t t (x t)| - `|f_t 0 (x 0)| <= `|f_t t (x t) - f_t 0 (x 0)|.
- exact: lerB_dist.
rewrite x_initial in ft_change diff_norm.
have htf : t \in f_domain_t.
- apply: integration_interval_in_f_domain_t.
  exact: ht.
have hx : x t \in f_domain_x.
- apply: solution_in_f_domain_x.
  exact: ht.
rewrite /acceleration.
apply: norm_sum_bound.
- by nra.
- apply: norm_product_bound.
  + apply: rk2_f_bound.
    * exact: htf.
    * exact: hx.
  + apply: rk2_f_x_bound.
    * exact: htf.
    * exact: hx.
Qed.

Local Lemma jerk_bound : {in `[0, T]%R, forall t : R, `|jerk t| <= M_3 ft_initial}.
Proof.
move=> t ht.
have htf : t \in f_domain_t.
- apply: integration_interval_in_f_domain_t.
  exact: ht.
have hx : x t \in f_domain_x.
- apply: solution_in_f_domain_x.
  exact: ht.
have bf : `|f t (x t)| <= M_f.
- apply: rk2_f_bound.
  + exact: htf.
  + exact: hx.
have bx : `|f_x t (x t)| <= M_x.
- apply: rk2_f_x_bound.
  + exact: htf.
  + exact: hx.
have bdfx : `|f_tx t (x t) + f_xx t (x t) * f t (x t)| <= M_tx + M_xx * M_f.
- apply: norm_sum_bound.
  + apply: rk2_f_tx_bound.
    * exact: htf.
    * exact: hx.
  + apply: norm_product_bound.
    * apply: rk2_f_xx_bound.
      -- exact: htf.
      -- exact: hx.
    * exact: bf.
rewrite /jerk.
apply: norm_sum_bound.
- apply: dft_along_bound.
  exact: ht.
- apply: norm_sum_bound.
  + apply: norm_product_bound.
    * exact: bf.
    * exact: bdfx.
  + apply: norm_product_bound.
    * exact: bx.
    * apply: acceleration_bound.
      exact: ht.
Qed.

Section AtStage.

Context (h : R) (n : nat).
Let t : R := t_n h n.
Context (hpos : 0 < h) (endT : t + h <= T).

Local Lemma step_time_ge0 : 0 <= t.
Proof.
apply: mulr_ge0.
- exact: ler0n.
- apply: ltW.
  exact: hpos.
Qed.

Local Lemma step_start_in_interval : t \in `[0, T]%R.
Proof.
move: step_time_ge0 hpos endT.
rewrite in_itv /=.
by lra.
Qed.

Local Lemma step_start_in_f_domain_t : t \in f_domain_t.
Proof.
apply: integration_interval_in_f_domain_t.
exact: step_start_in_interval.
Qed.

Local Lemma Phi_lipschitz (x1 x2 : R) :
  x1 \in f_domain_x -> x2 \in f_domain_x ->
  `|Phi h t x1 - Phi h t x2| <= L * `|x1 - x2|.
Proof.
move=> h1 h2.
pose dist := `|x1 - x2|.
pose accel := fun y : R => f_t t y + f t y * f_x t y.
have bf : `|f t x1 - f t x2| <= M_x * dist.
- apply: f_lipschitz.
  + exact: step_start_in_f_domain_t.
  + exact: h1.
  + exact: h2.
have bt : `|f_t t x1 - f_t t x2| <= M_tx * dist.
- apply: f_t_lipschitz.
  + exact: step_start_in_f_domain_t.
  + exact: h1.
  + exact: h2.
have bx : `|f_x t x1 - f_x t x2| <= M_xx * dist.
- apply: f_x_lipschitz.
  + exact: step_start_in_f_domain_t.
  + exact: h1.
  + exact: h2.
have bprod1 : `|f_x t x1 * (f t x1 - f t x2)| <= M_x * (M_x * dist).
- apply: norm_product_bound.
  + apply: rk2_f_x_bound.
    * exact: step_start_in_f_domain_t.
    * exact: h1.
  + exact: bf.
have bprod2 : `|f t x2 * (f_x t x1 - f_x t x2)| <= M_f * (M_xx * dist).
- apply: norm_product_bound.
  + apply: rk2_f_bound.
    * exact: step_start_in_f_domain_t.
    * exact: h2.
  + exact: bx.
have bd : `|accel x1 - accel x2| <=
    (M_tx + M_x ^+ 2 + M_f * M_xx) * dist.
- pose delta_ft := f_t t x1 - f_t t x2.
  pose f_x_delta_f := f_x t x1 * (f t x1 - f t x2).
  pose f_delta_fx := f t x2 * (f_x t x1 - f_x t x2).
  have decompose : accel x1 - accel x2 =
      delta_ft + f_x_delta_f + f_delta_fx.
  + rewrite /accel /delta_ft /f_x_delta_f /f_delta_fx.
    by ring.
  rewrite decompose.
  rewrite (_ : (M_tx + M_x ^+ 2 + M_f * M_xx) * dist =
      M_tx * dist + M_x * (M_x * dist) + M_f * (M_xx * dist)).
  + by ring.
  apply: norm_sum_bound.
  + apply: norm_sum_bound.
    * exact: bt.
    * exact: bprod1.
  + exact: bprod2.
have half0 : 0 <= h / 2.
- move: hpos.
  by lra.
have halfT : h / 2 <= T / 2.
- move: step_time_ge0 endT.
  by lra.
have scale : h / 2 * `|accel x1 - accel x2| <=
    T / 2 * ((M_tx + M_x ^+ 2 + M_f * M_xx) * dist).
- apply: ler_pM.
  + exact: half0.
  + exact: normr_ge0.
  + exact: halfT.
  + exact: bd.
rewrite /Phi.
rewrite opprD addrACA -mulrBr.
apply: le_trans.
- exact: ler_normD.
- rewrite normrM [`|h / 2|]ger0_norm //.
  rewrite /accel /dist in scale.
  rewrite /dist in bf.
  have enlarge : Phi_constant * `|x1 - x2| <= L * `|x1 - x2|.
  + apply: ler_wpM2r.
    * exact: normr_ge0.
    * rewrite /L.
      have phi_le : Phi_constant <= `|Phi_constant|.
      -- exact: ler_norm.
      by lra.
  rewrite /Phi_constant in enlarge.
  by lra.
Qed.

(* Differentiate the quadratic in its center, holding the endpoint b fixed. *)
Local Lemma quadratic_center_derivative (u v a : R -> R) (s b j : R) :
  is_derive s 1 u (v s) -> is_derive s 1 v (a s) -> is_derive s 1 a j ->
  is_derive s 1 (u + (cst b - id) * v + (cst b - id)^+2 * cst (2^-1 : R) * a)
    ((b - s)^+2 / 2 * j).
Proof.
move=> du dv da.
apply: is_derive_eq.
rewrite !fctE /GRing.scale /=.
by field.
Qed.

(* Taylor's quadratic evaluated at the step endpoint as its center s varies. *)
Local Lemma exact_Phi_remainder :
  `|x (t + h) - (x t + h * Phi h t (x t))| <= M_3 ft_initial * h ^+ 3.
Proof.
pose b := t + h.
pose velocity := along f.
pose poly := (x + (cst b - id) * velocity +
    (cst b - id)^+2 * cst (2^-1 : R) * acceleration)%R.
have step_in : {subset `[t, b]%R <= integration_interval}.
- move=> s.
  rewrite !in_itv /=.
  move=> /andP [ts sb].
  apply/andP.
  split.
  + apply: le_trans.
    * exact: step_time_ge0.
    * exact: ts.
  + apply: le_trans.
    * exact: sb.
    * exact: endT.
have dpoly (s : R) : s \in integration_interval ->
    is_derive s 1 poly ((b - s)^+2 / 2 * jerk s).
- move=> hs.
  rewrite /poly.
  apply: quadratic_center_derivative.
  + apply: x_ode.
    exact: hs.
  + rewrite /acceleration [f s (x s) * f_x s (x s)]mulrC.
    apply: f_solution_derivative.
    exact: hs.
  + apply: acceleration_derivative.
    exact: hs.
have lip : {in `[t, b]%R &, forall u v : R,
    `|poly u - poly v| <= (M_3 ft_initial * h^+2) * `|u - v|}.
- apply: lipschitz_of_derivative_bound_on_interval.
  + move=> s /step_in /dpoly [ds _].
    exact: ds.
  + move=> s hs.
    have hsT : s \in integration_interval.
    * apply: step_in.
      exact: hs.
    have [_ ds] : is_derive s 1 poly ((b - s)^+2 / 2 * jerk s).
    * apply: dpoly.
      exact: hsT.
    rewrite derive1n1 derive1E ds mulrC.
    apply: norm_product_bound.
    * apply: jerk_bound.
      exact: hsT.
    * move: hs.
      rewrite in_itv /= => /andP [ts sb].
      have bs0 : 0 <= b - s.
      -- by rewrite subr_ge0.
      rewrite ger0_norm.
      -- by nra.
      have bs_le_h : b - s <= h.
      -- rewrite /b.
         move: ts.
         by lra.
      have sq_le : (b - s)^+2 <= h^+2.
      -- apply: lerXn2r.
         ++ exact: bs0.
         ++ apply: ltW.
            exact: hpos.
         ++ exact: bs_le_h.
      by nra.
have tb : t <= b.
- rewrite /b.
  move: hpos.
  by lra.
have rem : `|poly b - poly t| <= (M_3 ft_initial * h ^+ 2) * `|b - t|.
- apply: lip.
  + by rewrite in_itv /= lexx andbT.
  + by rewrite in_itv /= lexx.
have at_end : poly b = x b.
- rewrite /poly !fctE /= subrr.
  by ring.
have at_start : poly t = x t + h * Phi h t (x t).
- rewrite /poly !fctE /velocity /acceleration /Phi /b /=.
  by field.
rewrite at_end at_start /b addrAC subrr add0r [`|h|]gtr0_norm // in rem.
rewrite [h ^+ 3]exprSr mulrA.
exact: rem.
Qed.

Let X : R := X_n f x_0 h n.
Context (hX : X \in f_domain_x).
Context (hK2 : K_2_in_domain h t X).

(* Taylor-expand K_2 in time, then in the state, with K_1 fixed. *)
Local Lemma K_2_taylor_remainder :
  `|K_2 f h t X - (K_1 f t X + f_t t X * (p * h) +
    K_1 f t X * f_x t X * (q * h))| <= M_K2 * h ^+ 2.
Proof.
move: hK2 => [hend hw].
pose dt := p * h.
pose dq := q * h.
pose dx := dq * K_1 f t X.
pose w := X + dx.
rewrite -/dq -/dx -/w in hw.
pose time_slice := fun s : R => f s w.
have et : `|time_slice (t + dt) - taylor_sum time_slice 1 t (t + dt)| <=
    M_tt * `|t + dt - t| ^+ 2.
- apply: rk2_taylor_bound.
  + exact: step_start_in_f_domain_t.
  + exact: hend.
  + move=> k hk s hs.
    apply: f_derivable_in_t.
    * exact: hs.
    * exact: hw.
    * exact: hk.
  + move=> s hs.
    apply: rk2_f_tt_bound.
    * exact: hs.
    * exact: hw.
rewrite taylor_linear in et.
rewrite /time_slice in et.
rewrite addrAC subrr add0r in et.
have dw : w - X = dx.
- by rewrite /w addrAC subrr add0r.
have ex : `|f t w - taylor_sum (f t) 1 X w| <= M_xx * `|w - X| ^+ 2.
- apply: rk2_taylor_bound.
  + exact: hX.
  + exact: hw.
  + move=> k hk y hy.
    apply: f_derivable_in_x.
    * exact: step_start_in_f_domain_t.
    * exact: hy.
    * exact: hk.
  + apply: rk2_f_xx_bound.
    exact: step_start_in_f_domain_t.
rewrite taylor_linear in ex.
rewrite dw in ex.
have em : `|f_t t w - f_t t X| <= M_tx * `|w - X|.
- apply: f_t_lipschitz.
  + exact: step_start_in_f_domain_t.
  + exact: hw.
  + exact: hX.
rewrite dw in em.
have K_1_bound : `|K_1 f t X| <= M_f.
- apply: rk2_f_bound.
  + exact: step_start_in_f_domain_t.
  + exact: hX.
have dx_bound : `|dx| <= `|dq| * M_f.
- apply: norm_product_bound.
  + exact: lexx.
  + exact: K_1_bound.
have hxx : 0 <= M_xx.
- apply: norm_bound_ge0.
  apply: rk2_f_xx_bound.
  + exact: step_start_in_f_domain_t.
  + exact: hX.
have htx : 0 <= M_tx.
- apply: norm_bound_ge0.
  apply: rk2_f_tx_bound.
  + exact: step_start_in_f_domain_t.
  + exact: hX.
have ex' : `|f t w - (K_1 f t X + f_x t X * dx)| <= M_xx * (`|dq| * M_f) ^+ 2.
- apply: le_trans.
  + exact: ex.
  + apply: ler_wpM2l.
    * exact: hxx.
    * apply: lerXn2r.
      -- exact: normr_ge0.
      -- apply: norm_bound_ge0.
         exact: dx_bound.
      -- exact: dx_bound.
have em' : `|(f_t t w - f_t t X) * dt| <= M_tx * (`|dq| * M_f) * `|dt|.
- apply: norm_product_bound.
  + by nra.
  + exact: lexx.
rewrite real_normK in et.
- exact: num_real.
have /ler_normlP [t_taylor_lo t_taylor_hi] :
    `|f (t + dt) w - (f t w + f_t t w * dt)| <= M_tt * dt ^+ 2.
- exact: et.
move/ler_normlP: ex' => [x_taylor_lo x_taylor_hi].
move/ler_normlP: em' => [mixed_lo mixed_hi].
have remainder_sum : M_tt * dt ^+ 2 + M_xx * (`|dq| * M_f) ^+ 2 +
    M_tx * (`|dq| * M_f) * `|dt| = M_K2 * h ^+ 2.
- rewrite /dt /dq /M_K2.
  rewrite !normrM [`|h|]gtr0_norm //.
  rewrite -[q ^+ 2]real_normK.
  + exact: num_real.
  by ring.
rewrite /K_2 -/dt -/dq -/dx -/w -remainder_sum.
rewrite /dx in x_taylor_lo x_taylor_hi.
rewrite ler_norml.
by lra.
Qed.

(* The order conditions give the same linear term in alpha * K_1 + beta * K_2 and Phi. *)
Local Lemma lemma1_Phi_K_1_K_2 :
  `|alpha * K_1 f t X + beta * K_2 f h t X - Phi h t X| <=
    `|beta| * (M_K2 * h ^+ 2).
Proof.
pose K_1 := K_1 f t X.
pose K_2 := K_2 f h t X.
pose linear_K2 := K_1 + f_t t X * (p * h) + K_1 * f_x t X * (q * h).
have match_Phi : alpha * K_1 + beta * linear_K2 = Phi h t X.
- change (alpha * K_1 + beta * linear_K2 =
      K_1 + h / 2 * (f_t t X + K_1 * f_x t X)).
  rewrite /linear_K2.
  rewrite (_ : alpha * K_1 + beta * (K_1 + f_t t X * (p * h) +
    K_1 * f_x t X * (q * h)) =
    (alpha + beta) * K_1 + h * ((beta * p) * f_t t X +
    (beta * q) * (K_1 * f_x t X))).
  + by ring.
  rewrite rk2_weights_sum rk2_order_t rk2_order_x.
  by field.
rewrite -/K_1 -/K_2 -match_Phi.
rewrite opprD addrACA subrr add0r -mulrBr.
rewrite normrM.
apply: ler_wpM2l.
- exact: normr_ge0.
- exact: K_2_taylor_remainder.
Qed.

Local Lemma numerical_Phi_remainder :
  `|rk2_step f h t X - (X + h * Phi h t X)| <=
    (`|beta| * M_K2) * h ^+ 3.
Proof.
rewrite /rk2_step.
rewrite opprD addrACA subrr add0r -mulrBr.
rewrite normrM [`|h|]gtr0_norm //.
rewrite (_ : (`|beta| * M_K2) * h ^+ 3 =
             h * (`|beta| * (M_K2 * h ^+ 2))).
- by ring.
apply: ler_wpM2l.
- apply: ltW.
  exact: hpos.
- exact: lemma1_Phi_K_1_K_2.
Qed.

(* Subtract the two expansions and apply the Lipschitz bound for Phi. *)
Local Lemma E_n_step :
  `|x (t + h) - rk2_step f h t X| <=
    (1 + h * L) * `|x t - X| + K ft_initial * h ^+ 3.
Proof.
move/ler_normlP: exact_Phi_remainder => [exact_lo exact_hi].
move/ler_normlP: numerical_Phi_remainder => [num_lo num_hi].
have /ler_normlP [phi_lo phi_hi] :
    `|Phi h t (x t) - Phi h t X| <= L * `|x t - X|.
- apply: Phi_lipschitz.
  + apply: solution_in_f_domain_x.
    exact: step_start_in_interval.
  + exact: hX.
have /ler_normlP [error_lo error_hi] : `|x t - X| <= `|x t - X|.
- exact: lexx.
have cubic_bound : (M_3 ft_initial + `|beta| * M_K2) * h ^+ 3 <= K ft_initial * h ^+ 3.
- apply: ler_wpM2r.
  + apply: exprn_ge0.
    apply: ltW.
    exact: hpos.
  + exact: ler_norm.
apply/ler_normlP.
split.
- move: hpos.
  by nra.
- move: hpos.
  by nra.
Qed.

Local Lemma E_n_recurrence :
  E_n h n.+1 <= (1 + h * L) * E_n h n + K ft_initial * h ^+ 3.
Proof.
rewrite /E_n t_nS.
exact: E_n_step.
Qed.

End AtStage.

Lemma rk2_error_radius_spec :
  let C := rk2_error_radius (f_t 0 x_0) in
  0 <= C /\ error_bound x C.
Proof.
split.
- apply: mulr_ge0.
  + rewrite subr_ge0 -expR0 ler_expR.
    apply: mulr_ge0.
    * apply: ltW.
      exact: L_positive.
    * apply: ltW.
      exact: T_pos.
  + apply: divr_ge0.
    * exact: normr_ge0.
    * apply: ltW.
      exact: L_positive.
- move=> h n hpos endT domains.
  change (E_n h n <= rk2_error_radius ft_initial * h ^+ 2).
  rewrite /rk2_error_radius.
  apply: E_n_exp_bound.
  + exact: hpos.
  + exact: L_positive.
  + exact: normr_ge0.
  + exact: endT.
  + exact: E_n_initial.
  + move=> i hin.
    have [hX hK2] : X_n f x_0 h i \in f_domain_x /\ K_2_in_domain h (t_n h i) (X_n f x_0 h i).
    * apply: domains.
      exact: hin.
    have grid_le : t_n h i.+1 <= t_n h n.
    * rewrite /t_n ler_pM2r //.
      by rewrite ler_nat.
    apply: E_n_recurrence.
    * exact: hpos.
    * rewrite -t_nS.
      apply: le_trans.
      -- exact: grid_le.
      -- exact: endT.
    * exact: hX.
    * exact: hK2.
Qed.

End ErrorForSolution.

Lemma rk2_global_error :
  exists2 x : R -> R,
    (x 0 = x_0 /\
    {in ode_interval problem, forall t : R, is_derive t 1 x (f t (x t))} /\
    {in ode_interval problem, forall t : R, x t \in f_domain_x}) &
    exists2 C : R, 0 <= C & error_bound x C.
Proof.
case: (ode_solution_exists problem) => x solution.
exists x.
- exact: solution.
- move: solution => [x_initial [x_ode solution_in_f_domain_x]].
  have [C_ge0 C_bound] : let C := rk2_error_radius ft_initial in
      0 <= C /\ error_bound x C.
  + apply: rk2_error_radius_spec.
    * exact: x_initial.
    * move=> t ht.
      apply: x_ode.
      apply: integration_interval_in_ode_interval.
      exact: ht.
    * move=> t ht.
      apply: solution_in_f_domain_x.
      apply: integration_interval_in_ode_interval.
      exact: ht.
  exists (rk2_error_radius ft_initial).
  + exact: C_ge0.
  + exact: C_bound.
Qed.

End RK2.
