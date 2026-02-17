From Perennial.algebra Require Import gen_heap_names.
From Perennial.program_logic Require Import dist_lang.
From Perennial.goose_lang Require Import lang lifting.
From Perennial.goose_lang Require Import ffi.grove_ffi.grove_ffi.

From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.

Set Default Proof Using "Type".

Existing Instances grove_op grove_model.
Existing Instances grove_semantics grove_interp.
Existing Instances goose_groveGS goose_groveNodeGS.
Theorem grove_ffi_dist_adequacy Σ {go_gctx : GoGlobalContext}
  {hGhost: all.allG Σ} `{hPre: !gooseGpreS Σ} ebσs g (φinv : _ → Prop) :
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
  intros H. eapply goose_dist_adequacy; try done.
  intros. iIntros "Hchan". iMod (H HG with "Hchan") as "(H1&H2)".
  iModIntro. iSplitL "H1".
  { iApply (big_sepL_mono with "H1").
    iIntros (? [e er σ] Hlookup) "H". iIntros. iSpecialize ("H" $! hG).
    iMod ("H" with "[$]") as "H".
    iDestruct "H" as (???) "H". iModIntro. iExists _, _, _. iFrame "H".
  }
  { eauto. }
Qed.

Theorem grove_ffi_dist_adequacy_failstop Σ {go_gctx : GoGlobalContext}
  {hGhost: all.allG Σ} `{hPre: !gooseGpreS Σ}
  (ebσs : list (goose_lang.expr * state)) g (φinv : _ → Prop) :
  (∀ HG : gooseGlobalGS Σ,
      ⊢@{iPropI Σ}
        ([∗ map] e↦ms ∈ g.(global_world).(grove_net), e c↦ ms) ={⊤}=∗
          (([∗ list] '(e, σ) ∈ ebσs,
                (* We reason about node running e with an arbitrary generation *)
                ∀ HL : gooseLocalGS Σ,
                  ([∗ map] f ↦ c ∈ σ.(world).(grove_node_files), f f↦ c) -∗
                  own_go_state σ.(go_state).(package_state)
                  ={⊤}=∗ ∃ Φ, wp NotStuck ⊤ e Φ
            ) ∗
          (∀ g', ffi_global_ctx goose_ffiGlobalGS g'.(global_world) ={⊤,∅}=∗ ⌜ φinv g' ⌝) )) →
  dist_adequate_failstop (ffi_sem:=grove_semantics) ebσs g (λ g, φinv g).
Proof.
  intros H. eapply goose_dist_adequacy_failstop; try done.
  intros. iIntros "Hchan". iMod (H HG with "Hchan") as "(H1&H2)".
  iModIntro. iSplitL "H1".
  { iApply (big_sepL_mono with "H1").
    iIntros (? [e σ] Hlookup) "H". iIntros. iApply ("H" with "[$] [$]"). }
  { eauto. }
Qed.

Theorem grove_ffi_single_node_adequacy_failstop Σ {go_gctx : GoGlobalContext}
  {hGhost: all.allG Σ} `{hPre: !gooseGpreS Σ} e σ g φ :
  (∀ (Hl : gooseLocalGS Σ) (Hg : gooseGlobalGS Σ),
    ⊢ ([∗ map] e↦ms ∈ g.(global_world).(grove_net), e c↦ ms) -∗
      ([∗ map] f ↦ c ∈ σ.(world).(grove_node_files), f f↦ c)
      ={⊤}=∗
      WP e @ ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate_failstop e σ g (λ v _ _, φ v).
Proof.
  intros. eapply goose_recv_adequacy_failstop; eauto; try done.
Qed.
