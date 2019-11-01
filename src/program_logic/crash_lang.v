From iris.program_logic Require Export language.
Set Default Proof Using "Type".

Structure crash_semantics (Λ: language) :=
  CrashSemantics {
      crash_prim_step : state Λ → state Λ → Prop;
      close_prim_step : state Λ → state Λ → Prop
  }.

Arguments crash_prim_step {_}.
Arguments close_prim_step {_}.

Section crash_language.
  Context {Λ: language}.
  Context {CS: crash_semantics Λ}.

  Inductive status : Set :=
  | Crashed
  | Normal.

  (* Execution with a recovery procedure. list nat argument counts
     steps in-between each crash. *)
  Inductive nrsteps (r: expr Λ) : list nat → cfg Λ → list (observation Λ) → cfg Λ → status → Prop :=
  | nrsteps_normal n ρ1 ρ2 κs:
      nsteps n ρ1 κs ρ2 →
      nrsteps r [n] ρ1 κs ρ2 Normal
  | nrsteps_crash n1 ns ρ1 ρ2 ρ3 σ κs1 κs2 s:
      nsteps n1 ρ1 κs1 ρ2 →
      crash_prim_step CS (ρ2.2) σ →
      nrsteps r ns ([r], σ) κs2 ρ3 s →
      nrsteps r (n1 :: ns) ρ1 (κs1 ++ κs2) ρ3 Crashed.

  Inductive erased_rsteps (r: expr Λ) : cfg Λ → cfg Λ → status → Prop :=
  | erased_rsteps_normal ρ1 ρ2:
      rtc erased_step ρ1 ρ2 →
      erased_rsteps r ρ1 ρ2 Normal
  | erased_rsteps_crash ρ1 ρ2 ρ3 σ s:
      rtc erased_step ρ1 ρ2 →
      crash_prim_step CS (ρ2.2) σ →
      erased_rsteps r ([r], σ) ρ3 s →
      erased_rsteps r ρ1 ρ3 Crashed.

  (* XXX: the sequence of programs to execute is non-adaptive in response to whether you crashed or not *)
  (*
  Inductive exec_seq (r: expr Λ) : nat →  list (expr Λ) → state Λ → list (observation Λ) → cfg Λ → Prop :=
  | exec_seq_empty σ:
      exec_seq r 0 [] σ [] ([], σ)
  | exec_seq_hd_finish n1 n2 e1 es σ1 σ2 ρ2 ρ3 κs1 κs2:
      ncsteps n1 ([e1], σ1) κs1 ρ2 Finish →
      close_prim_step CS (ρ2.2) σ2 →
      exec_seq r n2 es (ρ2.2) κs2 ρ3 →
      exec_seq r (n1 + n2) (e1 :: es) σ1 (κs1 ++ κs2) ρ3
  | exec_seq_hd_crash n1 n2 n3 e1 es σ1 ρ2 ρ3 ρ4 κs1 κs2 κs3:
      ncsteps n1 ([e1], σ1) κs1 ρ2 Finish →
      rexec r n2 (ρ2.2) κs2 ρ3 →
      exec_seq r n3 es (ρ3.2) κs3 ρ4 →
      exec_seq r (n1 + n2 + n3) (e1 :: es) σ1 (κs1 ++ κs2 ++ κs3) ρ4.
   *)
End crash_language.
