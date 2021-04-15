(** Defines the notion of a "distributed execution with crashes", and some
derived notions/lemmas. *)
From Perennial.program_logic Require Export language crash_lang.
From iris.prelude Require Import options.

Section dist_language.
  Context {Λ: language}.
  Context {CS: crash_semantics Λ}.

  Record dist_node :=
    { boot : expr Λ;
      tpool : list (expr Λ);
      local_state : state Λ }.

  Definition dist_cfg : Type := list dist_node * global_state Λ.

  Inductive dist_step : dist_cfg → list (observation Λ) → dist_cfg → Prop :=
  | dist_step_machine ρ1 κs ρ2 m eb t1 σ1 t2 σ2 :
      ρ1.1 !! m = Some {| boot := eb; tpool := t1; local_state := σ1 |} →
      ρ2.1 = <[ m := {| boot := eb; tpool := t2; local_state := σ2|}]> ρ1.1 →
      step (t1, (σ1,ρ1.2)) κs (t2, (σ2,ρ2.2)) →
      dist_step ρ1 κs ρ2
  | dist_step_crash ρ1 ρ2 m eb σ1 σ2 tp :
      ρ1.1 !! m = Some {| boot := eb; tpool := tp; local_state := σ1 |} →
      ρ2.1 = <[ m := {| boot := eb; tpool := [eb]; local_state := σ2 |}]> ρ1.1 →
      ρ2.2 = ρ1.2 →
      crash_prim_step CS σ1 σ2 →
      dist_step ρ1 [] ρ2.

  Inductive dist_nsteps : nat → dist_cfg → list (observation Λ) → dist_cfg → Prop :=
    | dist_nsteps_refl ρ :
       dist_nsteps 0 ρ [] ρ
    | dist_nsteps_l n ρ1 ρ2 ρ3 κ κs :
       dist_step ρ1 κ ρ2 →
       dist_nsteps n ρ2 κs ρ3 →
       dist_nsteps (S n) ρ1 (κ ++ κs) ρ3.
  Local Hint Constructors dist_nsteps : core.

  Definition erased_dist_step (ρ1 ρ2 : dist_cfg) := ∃ κ, dist_step ρ1 κ ρ2.

  Lemma erased_dist_steps_nsteps ρ1 ρ2 :
    rtc erased_dist_step ρ1 ρ2 ↔ ∃ n κs, dist_nsteps n ρ1 κs ρ2.
  Proof.
    split.
    - induction 1; firstorder eauto.
    - intros (n & κs & Hsteps). unfold erased_dist_step.
      induction Hsteps; eauto using rtc_refl, rtc_l.
  Qed.

  Definition not_stuck_node (dn: dist_node) (g: global_state Λ) :=
    ∀ e, e ∈ tpool dn → not_stuck e (local_state dn) g.

  (* Generate a dist_cfg from a list of boot programs and initial local states and a global state.
     Starting thread pool on each node is a single thread running boot code *)
  Definition starting_dist_cfg (eσs : list (expr Λ * state Λ)) g : dist_cfg :=
    (map (λ eσ, {| boot := fst eσ; local_state := snd eσ; tpool := [fst eσ] |}) eσs, g).

End dist_language.
