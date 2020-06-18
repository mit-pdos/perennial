(** Crash instances for fmcounter. *)
From iris.proofmode Require Import base tactics classes.
From Perennial.algebra Require Export fmcounter.
From Perennial.goose_lang Require Import crash_modality lifting.

Section instances.
Context `{ffi_semantics: ext_semantics}.
Context `{!ffi_interp ffi}.
Context `{!fmcounterG Σ, !heapG Σ}.

Global Instance fmcounter_lb_durable γ n:
  IntoCrash (fmcounter_lb γ n) (λ _, fmcounter_lb γ n).
Proof. rewrite /IntoCrash. iApply post_crash_nodep. Qed.

Global Instance fmcounter_durable γ q n:
  IntoCrash (fmcounter γ q n) (λ _, fmcounter γ q n).
Proof. rewrite /IntoCrash. iApply post_crash_nodep. Qed.
End instances.
