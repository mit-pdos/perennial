From Perennial.goose_lang.examples Require Import append_log.
From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import append_log_hocap.
From Perennial.goose_lang.ffi Require Import append_log_ffi.
From Perennial.goose_lang Require Import logical_reln spec_assert.
From Perennial.program_logic Require Import ghost_var.

Instance log_spec_ext : spec_ext_op := {| spec_ext_op_field := log_op |}.
Instance log_ffi_model : spec_ffi_model := {| spec_ffi_model_field := log_model |}.
Instance log_ext_semantics : spec_ext_semantics (log_spec_ext) (log_ffi_model) :=
  {| spec_ext_semantics_field := log_semantics |}.
Instance log_ffi_interp : spec_ffi_interp log_ffi_model :=
  {| spec_ffi_interp_field := log_interp |}.

Section refinement.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Context `{!refinement_heapG Σ}.
Context `{!lockG Σ, stagedG Σ}.
Context `{!logG Σ}.
Context `{Hin: inG Σ (authR (optionUR (exclR log_stateO)))}.
Context `{Hin_nat_ctx: inG Σ (authR (optionUR (exclR (leibnizO (nat * (spec_lang.(language.expr) →
                                                                       spec_lang.(language.expr)))))))}.
Context (SIZE: nat).
Context (SIZE_nonzero: 0 < SIZE).
Context (SIZE_bounds: int.nat SIZE = SIZE).
Existing Instances spec_ffi_model_field spec_ext_op_field spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Notation sstate := (@state (@spec_ext_op_field log_spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ext_op_field log_spec_ext)).
Notation sval := (@val (@spec_ext_op_field log_spec_ext)).

Definition Nlog := nroot.@"log".

Definition P (γ: gname) (s: log_state) :=
  match s with
  | UnInit => log_uninit_frag ∗ log_frag []
  | Initing  => log_uninit_frag ∗ log_frag []
  | Closed vs => log_closed_frag ∗ log_frag vs
  | Opening vs => log_closed_frag ∗ log_frag vs
  | Opened vs l => log_open l ∗ log_frag vs
  end%I.

Definition POpened := (∃ l, log_open l)%I.
Definition PStartedOpening γ :=
  (∃ j (K: spec_lang.(language.expr) → spec_lang.(language.expr)) (Hctx: LanguageCtx K),
      j ⤇ K (ExternalOp (ext := spec_ext_op_field) OpenOp #())
      ∗ own γ (● Excl' ((j, K) : leibnizO (nat * (sexpr → sexpr)))))%I.
Definition PStartedIniting γ :=
  (∃ j (K: spec_lang.(language.expr) → spec_lang.(language.expr)) (Hctx: LanguageCtx K),
      j ⤇ K (ExternalOp (ext := spec_ext_op_field) InitOp #())
      ∗ own γ (● Excl' ((j, K) : leibnizO (nat * (sexpr → sexpr)))))%I.

Lemma PStartedOpening_Timeless γ : Timeless (PStartedOpening γ).
Proof. apply _. Qed.
Lemma PStartedIniting_Timeless γ : Timeless (PStartedIniting γ).
Proof. apply _. Qed.

Definition log_inv γ : nat → iProp Σ :=
  log_inv Nlog (P γ) (POpened) (PStartedOpening γ) (PStartedIniting γ) SIZE.
Definition is_log γ : nat → loc → iProp Σ :=
  is_log Nlog (P γ) (POpened) (PStartedOpening γ) (PStartedIniting γ) SIZE.

Theorem wpc_Init j γ K k k' E2:
  (S k < k')%nat →
  {{{ spec_ctx ∗ log_inv γ k' ∗ j ⤇ K (ExternalOp (ext := spec_ext_op_field) InitOp #()) }}}
    Init #SIZE @ NotStuck; LVL (S (S (S k))); ⊤; E2
  {{{ l, RET (#l, #true);  is_log γ k' l ∗ j ⤇ K (of_val (#l, #true) : sexpr)}}}
  {{{ True }}}.
Proof.
  iIntros (? Φ Φc) "(#Hspec&#Hinv&Hj) HΦ".
  wpc_apply (wpc_Init _ _ _ _ _ _ _ _ _ _ _ _ (True%I) (λ l, j ⤇ K (of_val (#l, #true)))%I
               with "[Hj]"); try iFrame "Hinv"; eauto.
  iSplit; [| iSplit].
  - iIntros (vs); simpl P.
    iIntros "(Hclosed&Hlist)".
    iDestruct "Hspec" as "(#Hspec&#Hstate)".
    iInv "Hstate" as (?) "(>H&Hinterp)" "Hclo".
    iDestruct "Hinterp" as "(?&>Hffi&?&?)".
    rewrite /spec_interp.

Abort.

End refinement.
