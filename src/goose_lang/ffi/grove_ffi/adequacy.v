From Perennial.algebra Require Import gen_heap_names.
From Perennial.program_logic Require Import dist_lang.
From Perennial.goose_lang Require Import lang notation lifting.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.grove_ffi.grove_ffi.

From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.

Set Default Proof Using "Type".

Existing Instances grove_op grove_model.
Existing Instances grove_semantics grove_interp.
Existing Instances goose_groveGS goose_groveNodeGS.
Theorem grove_ffi_dist_adequacy Σ `{hPre: !gooseGpreS Σ} ebσs g (φinv : _ → Prop) :
  chan_msg_bounds g.(global_world).(grove_net) →
  Forall (λ ρ, file_content_bounds ρ.(init_local_state).(world).(grove_node_files)) ebσs →
  (∀ HG : gooseGlobalGS Σ,
      ⊢@{iPropI Σ}
        ([∗ map] e↦ms ∈ g.(global_world).(grove_net), e c↦ ms) ={⊤}=∗
          (([∗ list] ρ ∈ ebσs,
                (* We reason about node running e with an arbitrary generation *)
                ∀ HL : gooseLocalGS Σ,
                  ([∗ map] f ↦ c ∈ ρ.(init_local_state).(world).(grove_node_files), f f↦ c)
                    ={⊤}=∗ ∃ Φ Φc Φr, wpr NotStuck ⊤ ρ.(init_thread) ρ.(init_restart) Φ Φc Φr) ∗
          (∀ g', ffi_global_ctx goose_ffiGlobalGS g'.(global_world) ={⊤,∅}=∗ ⌜ φinv g' ⌝) )) →
  dist_adequacy.dist_adequate (CS := goose_crash_lang) ebσs g (λ g, φinv g).
Proof.
  intros HINITG HINIT H. eapply goose_dist_adequacy; eauto.
  { simpl. intros σ Hσ.
    apply list_elem_of_fmap in Hσ as (ρ&Heq&Hin).
    rewrite Heq.
    eapply Forall_forall in HINIT; last done. eauto. }
  intros. iIntros "Hchan". iMod (H HG with "Hchan") as "(H1&H2)".
  iModIntro. iSplitL "H1".
  { iApply (big_sepL_mono with "H1").
    iIntros (? [e er σ] Hlookup) "H". iIntros. iSpecialize ("H" $! hG).
    iMod ("H" with "[$]") as "H".
    iDestruct "H" as (???) "H". iModIntro. iExists _, _, _. iFrame "H".
  }
  { eauto. }
Qed.

Theorem grove_ffi_dist_adequacy_failstop Σ `{hPre: !gooseGpreS Σ}
  (ebσs : list (goose_lang.expr * goose_lang.state)) g (φinv : _ → Prop) :
  chan_msg_bounds g.(global_world).(grove_net) →
  Forall (λ σ, file_content_bounds σ.(world).(grove_node_files)) ebσs.*2 →
  (∀ HG : gooseGlobalGS Σ,
      ⊢@{iPropI Σ}
        ([∗ map] e↦ms ∈ g.(global_world).(grove_net), e c↦ ms) ={⊤}=∗
          (([∗ list] '(e, σ) ∈ ebσs,
                (* We reason about node running e with an arbitrary generation *)
                ∀ HL : gooseLocalGS Σ,
                  ([∗ map] f ↦ c ∈ σ.(world).(grove_node_files), f f↦ c) -∗
                  own_globals (DfracOwn 1) σ.(globals)
                  ={⊤}=∗ ∃ Φ, wp NotStuck ⊤ e Φ
            ) ∗
          (∀ g', ffi_global_ctx goose_ffiGlobalGS g'.(global_world) ={⊤,∅}=∗ ⌜ φinv g' ⌝) )) →
  dist_adequate_failstop (ffi_sem:=grove_semantics) ebσs g (λ g, φinv g).
Proof.
  intros HINITG HINIT H. eapply goose_dist_adequacy_failstop; eauto.
  { simpl.  intros σ Hσ. eapply Forall_forall in HINIT; last done. eauto. }
  intros. iIntros "Hchan". iMod (H HG with "Hchan") as "(H1&H2)".
  iModIntro. iSplitL "H1".
  { iApply (big_sepL_mono with "H1").
    iIntros (? [e σ] Hlookup) "H". iIntros. iApply ("H" with "[$] [$]"). }
  { eauto. }
Qed.

Theorem grove_ffi_single_node_adequacy_failstop Σ `{hPre: !gooseGpreS Σ} e σ g φ :
  chan_msg_bounds g.(global_world).(grove_net) →
  file_content_bounds σ.(world).(grove_node_files) →
   (∀ `(Hheap : !heapGS Σ),
    ⊢ ([∗ map] e↦ms ∈ g.(global_world).(grove_net), e c↦ ms) -∗
      ([∗ map] f ↦ c ∈ σ.(world).(grove_node_files), f f↦ c)
      ={⊤}=∗
      WP e @ ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate_failstop e σ g (λ v _ _, φ v).
Proof.
  intros. eapply goose_recv_adequacy_failstop; eauto.
Qed.
