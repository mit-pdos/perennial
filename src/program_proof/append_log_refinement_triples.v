From Perennial.goose_lang.examples Require Import append_log.
From Perennial.goose_lang.lib Require Import encoding crash_lock.
From Perennial.base_logic Require Import ghost_var.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import append_log_hocap.
From Perennial.goose_lang.ffi Require Import append_log_ffi.
From Perennial.goose_lang Require Import spec_assert refinement_adequacy.

Existing Instances log_spec_ext log_spec_ffi_model log_spec_ext_semantics log_spec_ffi_interp log_spec_interp_adequacy.

Section refinement.
Context `{!heapG Σ}.
Context `{!refinement_heapG Σ}.
Context `{stagedG Σ}.
Existing Instance logG0.
Context `{Hin: inG Σ (authR (optionUR (exclR log_stateO)))}.
Context `{Hin_nat_ctx: inG Σ (authR (optionUR (exclR (leibnizO (nat * (spec_lang.(language.expr) →
                                                                       spec_lang.(language.expr)))))))}.
Context (SIZE: nat).
Context (SIZE_nonzero: 0 < SIZE).
Context (SIZE_bounds: int.nat SIZE = SIZE).
Existing Instances spec_ffi_model_field spec_ffi_op_field spec_ext_semantics_field (* spec_ffi_interp_field  *) spec_ffi_interp_adequacy_field.

Notation sstate := (@state (@spec_ffi_op_field log_spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ffi_op_field log_spec_ext)).
Notation sval := (@val (@spec_ffi_op_field log_spec_ext)).

Definition Nlog := nroot.@"log".

Definition thread_tok_frag γ j K :=
  own γ (◯E ((j, K) : leibnizO (nat * (sexpr → sexpr)))).
Definition thread_tok_auth γ j K :=
  own γ (●E ((j, K) : leibnizO (nat * (sexpr → sexpr)))).
Definition thread_tok_full γ j K :=
 (thread_tok_auth γ j K ∗ thread_tok_frag γ j K)%I.

Definition P (γ: gname) (s: log_state) :=
  match s with
  | UnInit => log_uninit_frag ∗ log_frag [] ∗ thread_tok_full γ 0 id
  | Initing  => log_uninit_frag ∗ log_frag []
  | Closed vs => log_closed_frag ∗ log_frag vs ∗ thread_tok_full γ 0 id
  | Opening vs => log_closed_frag ∗ log_frag vs
  | Opened vs l => (∃ l', log_open l' ∗ log_frag vs)
  end%I.

Definition POpened := (∃ l, log_open l)%I.
Definition PStartedOpening γ :=
  (∃ j (K: spec_lang.(language.expr) → spec_lang.(language.expr)) (Hctx: LanguageCtx K),
      j ⤇ K (ExternalOp (ext := spec_ffi_op_field) OpenOp #())
      ∗ thread_tok_auth γ j K)%I.
Definition PStartedIniting γ :=
  (∃ j (K: spec_lang.(language.expr) → spec_lang.(language.expr)) (Hctx: LanguageCtx K),
      j ⤇ K (ExternalOp (ext := spec_ffi_op_field) InitOp #())
      ∗ thread_tok_auth γ j K)%I.

Lemma PStartedOpening_Timeless γ : Timeless (PStartedOpening γ).
Proof. apply _. Qed.
Lemma PStartedIniting_Timeless γ : Timeless (PStartedIniting γ).
Proof. apply _. Qed.

Definition log_inv γ : nat → iProp Σ :=
  log_inv Nlog (P γ) (POpened) (PStartedOpening γ) (PStartedIniting γ) SIZE.
Definition is_log γ : nat → loc → iProp Σ :=
  is_log Nlog (P γ) (POpened) (PStartedOpening γ) (PStartedIniting γ) SIZE.

Theorem wpc_Init j γ K `{LanguageCtx _ K} k k' E2:
  (S k < k')%nat →
  {{{ spec_ctx ∗ log_inv γ k' ∗ j ⤇ K (ExternalOp (ext := spec_ffi_op_field) InitOp #()) }}}
    Init #SIZE @ NotStuck; LVL (S (S k)); ⊤; E2
  {{{ l, RET (#l, #true);  is_log γ k' l ∗ (∃ (l': loc), j ⤇ K (of_val (#l', #true) : sexpr) ∗ log_open l')}}}
  {{{ True }}}.
Proof using SIZE_nonzero SIZE_bounds.
  iIntros (? Φ Φc) "(#Hspec&#Hinv&Hj) HΦ".
  unshelve
    wpc_apply (wpc_Init _ _ _ _ _ _ _ _ _ _ _ _ (True%I)
                        (λ l, (∃ (l': loc), j ⤇ K (of_val (#l', #true)) ∗ log_open l'))%I
               with "[Hj]"); try iFrame "Hinv"; eauto.
  { apply _. }
  iSplit; [| iSplit].
  - iIntros (vs); simpl P.
    iIntros "(Hclosed&Hlist&Htok)".
    iMod (log_closed_init_false with "[$] [$] [$] Hj") as %[].
    { solve_ndisj. }
  - iIntros "[Hiniting|[Hopening|Hopened]]".
    * iDestruct "Hiniting" as (j' K' Hctx') "(Hj'&_)".
      iMod (log_init_init_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
    * iDestruct "Hopening" as (j' K' Hctx') "(Hj'&_)".
      iMod (log_init_open_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
    * iDestruct "Hopened" as (l) "Hopen".
      iMod (log_opened_init_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
  - iSplit; last done. simpl.
    iIntros "(Huninit_frag&Hvals_frag&(Hthread_auth&Hthread_frag))".
    iMod (ghost_var_update _ ((j, K) : leibnizO (nat * (sexpr → sexpr))) with "[$] [$]")
         as "(Hthread_auth&Hthread_frag)".
    iModIntro.
    iSplitL "Hthread_auth Hj".
    { unshelve (iExists _, _, _; iFrame); eauto. }
    iFrame. iSplit; first done.
    iIntros (l) "(Huninit&Hvals) Hthread".
    iDestruct "Hthread" as (j' K' ?) "(Hj&Hthread_auth)".
    rewrite /thread_tok_auth.
    unify_ghost.
    iMod (ghost_step_log_init with "[$] [$] [$] [$]") as (l') "(Hj&#Hopen&Hvals)".
    { solve_ndisj. }
    iModIntro. iSplitR "Hvals".
    * iExists _. iFrame. iFrame "Hopen".
    * iFrame. iSplitL ""; iExists _; iFrame "Hopen".
Qed.

Theorem wpc_Open j γ K `{LanguageCtx _ K} k k' E2:
  (S k < k')%nat →
  {{{ spec_ctx ∗ log_inv γ k' ∗ j ⤇ K (ExternalOp (ext := spec_ffi_op_field) OpenOp #()) }}}
    Open #() @ NotStuck; LVL (S (S k)); ⊤; E2
  {{{ l, RET #l;  is_log γ k' l ∗ (∃ (l': loc), j ⤇ K (of_val #l': sexpr) ∗ log_open l')}}}
  {{{ True }}}.
Proof using SIZE_bounds.
  iIntros (? Φ Φc) "(#Hspec&#Hinv&Hj) HΦ".
  unshelve
  wpc_apply (wpc_Open _ _ _ _ _ _ _ _ _ _ (True%I) (λ l, (∃ (l': loc), j ⤇ K (of_val #l') ∗ log_open l'))%I
               with "[Hj]"); try iFrame "Hinv"; eauto.
  { apply _. }
  iSplit; [| iSplit].
  - iIntros "(Huninit&Hlist&Htok)".
    iMod (log_uninit_open_false with "[$] [$] [$] Hj") as %[].
    { solve_ndisj. }
  - iIntros "[Hiniting|[Hopening|Hopened]]".
    * iDestruct "Hiniting" as (j' K' Hctx') "(Hj'&_)".
      iMod (log_init_open_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
    * iDestruct "Hopening" as (j' K' Hctx') "(Hj'&_)".
      iMod (log_open_open_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
    * iDestruct "Hopened" as (l) "Hopen".
      iMod (log_opened_open_false with "[$] [$] [$]") as %[].
      { solve_ndisj. }
  - iSplit; last done. simpl.
    iIntros (vs) "(Hclosed_frag&Hvals_frag&(Hthread_auth&Hthread_frag))".
    iMod (ghost_var_update _ ((j, K) : leibnizO (nat * (sexpr → sexpr))) with "[$] [$]")
         as "(Hthread_auth&Hthread_frag)".
    iModIntro.
    iSplitL "Hthread_auth Hj".
    { unshelve (iExists _, _, _; iFrame); eauto. }
    iFrame. iSplit; first done.
    iIntros (l) "(Huninit&Hvals) Hthread".
    iDestruct "Hthread" as (j' K' ?) "(Hj&Hthread_auth)".
    rewrite /thread_tok_auth.
    unify_ghost.
    iMod (ghost_step_log_open with "[$] [$] [$] [$]") as (l') "(Hj&#Hopen&Hvals)".
    { solve_ndisj. }
    iModIntro. iSplitR "Hvals".
    * iExists _. iFrame. iFrame "Hopen".
    * iFrame. iSplitL ""; iExists _; iFrame "Hopen".
Qed.

Theorem wpc_Log__Reset j γ γ0 K `{LanguageCtx _ K} k k' E2 (l l': loc):
  (S (S k) < k')%nat →
  {{{ spec_ctx ∗ log_inv γ0 k' ∗ j ⤇ K (ExternalOp (ext := spec_ffi_op_field) (ResetOp) #l') ∗
               is_log γ k' l ∗ log_open l'
  }}}
    Log__Reset #l @ NotStuck; (LVL (S (S k))); ⊤; E2
  {{{ RET #(); j ⤇ K (of_val #(): sexpr)}}}
  {{{ True }}}.
Proof using SIZE_bounds.
  iIntros (? Φ Φc) "(#Hspec&#Hinv&Hj&His_log&#Hopen) HΦ".
  wpc_apply (wpc_Log__Reset _ _ _ _ _ _ _ _ _ _ (j ⤇ K (of_val #()))%I True%I
               with "[Hj His_log Hopen]"); try iFrame "His_log"; eauto.
  iSplit; last done.
  iIntros (bs).
  iIntros "Hopened". iDestruct "Hopened" as (?) "(_&Hfrag)".
  iMod (ghost_step_log_reset with "[$] [$] [$] [$]") as "(Hj&Hvals)".
  { solve_ndisj. }
  iModIntro. iFrame. iExists _. eauto.
Qed.


End refinement.

