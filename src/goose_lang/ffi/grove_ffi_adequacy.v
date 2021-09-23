From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import lang notation typing lifting.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.grove_prelude.

From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.
From Perennial.program_proof Require Import grove_prelude.

Set Default Proof Using "Type".

Section grove_ffi_adeq.

Theorem grove_ffi_dist_adequacy_failstop Σ `{hPre: !gooseGpreS Σ} (ebσs : list (expr * state))
        g φinv (HINITG: ffi_initgP g) :
  (∀ HG : gooseGlobalGS Σ,
      ⊢@{iPropI Σ}
        ([∗ map] e↦ms ∈ g, e c↦ ms) ={⊤}=∗
          (([∗ list] ebσ ∈ ebσs,
                let e := fst ebσ in
                (* We reason about node running e with an arbitrary generation *)
                ∀ HL : gooseLocalGS Σ,
                  |={⊤}=> ∃ Φ, wp NotStuck ⊤ e Φ) ∗
          (∀ g', ffi_global_ctx goose_ffiGlobalGS g' ={⊤,∅}=∗ ⌜ φinv g' ⌝) )) →
  dist_adequate_failstop (ffi_sem:=grove_semantics) ebσs g (λ g, φinv g).
Proof.
  intros. eapply goose_dist_adequacy_failstop; eauto.
  { simpl. eauto. }
  intros. iIntros "Hchan". iMod (H HG with "Hchan") as "(H1&H2)".
  iModIntro. iSplitL "H1".
  { iApply (big_sepL_mono with "H1").
    iIntros (?? Hlookup) "H". iIntros. iApply "H". }
  { eauto. }
Qed.
End grove_ffi_adeq.

