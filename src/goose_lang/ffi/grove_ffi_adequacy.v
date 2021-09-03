From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import lang notation typing lifting.
From Perennial.goose_lang.lib Require Import map.impl list.impl list_slice.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.


From Perennial.goose_lang Require Import adequacy recovery_adequacy dist_adequacy.
From Perennial.program_proof Require Import grove_prelude.

Set Default Proof Using "Type".

Section grove_ffi_adeq.

Local Instance groveGS_adeq {Σ} `{hPre: !heapGpreS Σ} : dist_heapGS Σ → groveGS Σ.
Proof.
  intros Hheap.
  apply (@grove_update_pre Σ
                           dist_heapGpreS.(@heap_preG_ffi _ _ _ _ (grove_interp_adequacy) Σ)
                                            (@dist_heapGS_names _ _ _ _ grove_interp_adequacy _ _)).
Defined.

Theorem grove_ffi_dist_adequacy_failstop Σ `{hPre: !heapGpreS Σ} (ebσs : list (expr * state))
        g φinv (HINITG: ffi_initgP g) :
  (∀ `{Hheap : !dist_heapGS Σ},
      ⊢
        ([∗ map] e↦ms ∈ g, e c↦ ms) ={⊤}=∗
          (([∗ list] ebσ ∈ ebσs,
                let e := fst ebσ in
                (* We reason about node running e with an arbitrary crash and heap name *)
                ∀ Hcrash heap_name,
                  let _ := dist_heapGS_heapGS Hheap Hcrash heap_name in
                  |={⊤}=> ∃ Φ, wp NotStuck ⊤ e Φ) ∗
          (∀ g', gen_heap_interp g' ∗ ⌜grove_ffi.chan_msg_bounds g'⌝ ={⊤,∅}=∗ ⌜ φinv g' ⌝))) →
  dist_adequate_failstop ebσs g (λ g, φinv g).
Proof.
  intros. eapply heap_dist_adequacy_failstop; eauto.
  { simpl. eauto. }
  { intros. iIntros "Hchan". iMod (H _ with "[Hchan]") as "(H1&H2)".
    { iDestruct "Hchan" as "($&_)". }
    iModIntro. iSplitL "H1".
    { iApply (big_sepL_mono with "H1").
      iIntros (?? Hlookup) "H". iIntros. iApply "H". }
    { eauto. }
  }
Qed.
End grove_ffi_adeq.

