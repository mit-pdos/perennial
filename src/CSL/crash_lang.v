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
  | Pending
  | Crash
  | Finish.

  (* This relation either:
     (1) simulates a step (cstep_step)
     (2) marks a process as finished (if parent is a vlaue) (cstep_finish)
     (3) marks a process as about to crash (cstep_crash)
   *)
  Inductive cstep (ρ1 : cfg Λ) (κ : list (observation Λ)) (ρ2 : cfg Λ) : status → Prop :=
  | cstep_step :
      step ρ1 κ ρ2 →
      cstep ρ1 κ ρ2 Pending
  | cstep_finish v t σ :
      ρ1 = (of_val v :: t, σ) →
      ρ2 = ρ1 →
      cstep ρ1 κ ρ2 Finish
  | cstep_crash t σ1 :
      ρ1 = (t, σ1) →
      ρ2 = ρ1 →
      cstep ρ1 κ ρ2 Crash.

  (* XXX: consider using kleene algebra combinators for these. however, even in
          the shallow embedding, ultimately had to define alternate forms that
          count the number of steps taken, in order to do the step-indexing
          proof, and then I proved an equivalence.
          (though maybe that means that the true right thing to do is
          define a model of the Kleene Algebra transitions that counts the steps
          *)

  (* Repeatedly do cstep, so long as still pending, and count
     total number of steps taken *)
  Inductive ncsteps : nat → cfg Λ → list (observation Λ) → cfg Λ → status → Prop :=
    | ncsteps_refl ρ stat :
       ncsteps 0 ρ [] ρ stat
    | ncsteps_l n ρ1 ρ2 ρ3 κ κs stat :
       cstep ρ1 κ ρ2 Pending →
       ncsteps n ρ2 κs ρ3 stat →
       ncsteps (S n) ρ1 (κ ++ κs) ρ3 stat.

  (* A complete execution of a recovery procedure, with possibly several
     intermediate crashes *)
  Inductive rexec (r: expr Λ) : nat → state Λ → list (observation Λ) → cfg Λ → Prop :=
  | rexec_fin n σ1 ρ2 κs:
      ncsteps n ([r], σ1) κs ρ2 Finish →
      rexec r n σ1 κs ρ2
  | rexec_crash n1 n2 σ1 σ2 ρ2 ρ3 κs1 κs2:
      ncsteps n1 ([r], σ1) κs1 ρ2 Crash →
      crash_prim_step CS (ρ2.2) σ2 →
      rexec r n2 σ2 κs2 ρ3 →
      rexec r (n1 + n2) σ1 (κs1 ++ κs2) ρ3.

  (* XXX: the sequence of programs to execute is non-adaptive in response to whether you crashed or not *)
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
End crash_language.
