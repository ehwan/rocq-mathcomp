From mathcomp Require Import boot order ssralg ssrnum interval.
From mathcomp Require Import classical_sets reals filter topology normedtype derive.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ODE.
Context (R : realType).

(* Scalar initial value problem with f = ode_f continuous on ode_f_domain_t × ode_f_domain_x.
     x'(t) = f(t, x(t)),   x(t) ∈ ode_f_domain_x    for t ∈ ode_interval
     x(0)  = ode_x_0,      0 ∈ ode_interval ⊆ ode_f_domain_t *)
Record ode := {
  ode_f : R -> R -> R;
  ode_f_domain_t : interval R;
  ode_f_domain_x : interval R;
  ode_interval : interval R;
  ode_x_0 : R;
  ode_zero_in_interval : 0 \in ode_interval;
  ode_interval_in_domain_t : {subset ode_interval <= ode_f_domain_t};
  ode_continuous : {within [set` ode_f_domain_t] `*` [set` ode_f_domain_x],
    continuous (fun z : R * R => ode_f z.1 z.2)}
}.

Context (problem : ode).

Lemma ode_solution_exists :
  exists x : R -> R,
    x 0 = ode_x_0 problem /\
    {in ode_interval problem, forall t : R, is_derive t 1 x (ode_f problem t (x t))} /\
    {in ode_interval problem, forall t : R, x t \in ode_f_domain_x problem}.
Proof.
Admitted.

End ODE.
