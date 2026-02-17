From New.proof Require Export proof_prelude.
From New.proof.sync_proof Require Import base.
From New.proof.sync_proof Require Import waitgroup.
From Perennial Require Export base.

Module join.
Section waitgroup_join_idiom.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : sync.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Record WaitGroup_join_names :=
  {
    wg_gn : WaitGroup_names;
    wg_aprop_gn : gname;
    wg_not_done_gn : gname;
  }.

Implicit Types γ : WaitGroup_join_names.

Local Definition wgjN := nroot.@"wgjoin".

(* Internal invariant. Maintains ownership of the waitgroup counter so that
   Done() can run concurrently to Add. *)
Local Definition is_wgj_inv wg γ : iProp Σ :=
  "#His" ∷ is_WaitGroup wg γ.(wg_gn) (wgjN.@"wg") ∗
  "#Hinv" ∷
  inv (wgjN.@"inv") (
      ∃ ctr added done Pdone,
        "Hwg_ctr" ∷ own_WaitGroup γ.(wg_gn) ctr ∗
        "Hadded" ∷ own_tok_auth_dfrac γ.(wg_not_done_gn) (DfracOwn (1/2)) added ∗
        "Hdone_toks" ∷ own_toks γ.(wg_not_done_gn) done ∗
        "Hdone_aprop" ∷ own_aprop_frag γ.(wg_aprop_gn) Pdone done ∗
        "Hdone_P" ∷ Pdone ∗
        "%Hctr_pos" ∷ (⌜ 0 ≤ sint.Z ctr ⌝) ∗
        "%Hctr" ∷ (⌜ sint.Z ctr = Z.of_nat added - Z.of_nat done ⌝)
    ).

(** Permission to call `Add` or ``Wait`. Calling `Add` will extend `P` with a
    caller-chosen proposition (as long as `num_added` doesn't overflow) and
    calling `Wait` will give `P` as postcondition and reset the permission. *)
Definition own_Adder wg (num_added : w32) (P : iProp Σ) : iProp Σ :=
  ∃ γ P',
  "Hno_waiters" ∷ own_WaitGroup_waiters γ.(wg_gn) 0 ∗
  "Haprop" ∷ own_aprop_auth γ.(wg_aprop_gn) P' (sint.nat num_added) ∗
  "Hadded" ∷ own_tok_auth_dfrac γ.(wg_not_done_gn) (DfracOwn (1/2)) (sint.nat num_added) ∗
  "%Hadded_pos" ∷ ⌜ 0 ≤ sint.Z num_added ⌝ ∗
  "HimpliesP" ∷ (P' -∗ P) ∗
  "#Hinv" ∷ is_wgj_inv wg γ.
#[global] Opaque own_Adder.
#[local] Transparent own_Adder.

(** Permission to call `Done` as long as `P` is passed in. *)
Definition own_Done wg (P : iProp Σ) : iProp Σ :=
  ∃ γ,
  "Haprop" ∷ own_aprop γ.(wg_aprop_gn) P ∗
  "Hdone_tok" ∷ own_toks γ.(wg_not_done_gn) 1 ∗
  "#Hinv" ∷ is_wgj_inv wg γ.
#[global] Opaque own_Done.
#[local] Transparent own_Done.

Lemma init wg γwg :
  is_WaitGroup wg γwg (wgjN.@"wg") ∗
  own_WaitGroup γwg (W32 0) ∗
  own_WaitGroup_waiters γwg 0 ={⊤}=∗
  own_Adder wg (W32 0) True.
Proof.
  iIntros "(#His & Hctr_inv & Hwaiters)".
  iMod own_aprop_auth_alloc as (wg_aprop_gn) "Haprop".
  iMod own_tok_auth_alloc as (wg_not_done_gn) "[Hadded_inv Hadded]".
  iExists _. instantiate (1:=ltac:(econstructor)). rewrite /own_Adder /=.
  iFrame. iSplitR; first word.
  iMod own_toks_0 as "?". iDestruct own_aprop_frag_0 as "?".
  iSplitR; first by iIntros "!# ?".
  iMod (inv_alloc with "[-]") as "$"; last done.
  iFrame "∗#". word.
Qed.

Lemma wp_WaitGroup__Add P' wg P num_added :
  {{{ is_pkg_init sync ∗
      "Ha" ∷ own_Adder wg num_added P ∗
      "%Hoverflow" ∷ (⌜ sint.Z num_added < 2^31-1 ⌝)
  }}}
    wg @! (go.PointerType sync.WaitGroup) @! "Add" #(W64 1)
  {{{ RET #();
      own_Adder wg (word.add num_added (W32 1)) (P ∗ P') ∗
      own_Done wg P'
  }}}.
Proof.
  wp_start_folded as "Hpre". iNamed "Hpre". iNamed "Ha". iNamed "Hinv".
  wp_apply (wp_WaitGroup__Add with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
  iNamedSuffix "Hi" "_inv". iExists _; iFrame.
  iCombine "Hadded Hadded_inv" gives %[_ Heq]. subst.
  iSplitR; first word.
  iRight. iFrame.
  iIntros "Hno_waiters".
  iIntros "Hwg_ctr_inv". iMod "Hmask" as "_".
  iMod (own_aprop_auth_add P' with "Haprop") as "[Haprop Hdone_aprop]".
  iCombine "Hadded Hadded_inv" as "Hadded".
  iMod (own_tok_auth_S with "Hadded") as "[[Hadded Hadded_inv] Hdone_tok]".
  iCombineNamed "*_inv" as "Hi".
  iMod ("Hclose" with "[Hi]").
  { iNamed "Hi". iFrame. word. }
  iModIntro. iApply "HΦ". iFrame "∗#".
  progress replace (S _) with (sint.nat (word.add num_added $ W32 1)) by word.
  progress replace (sint.nat (word.add _ _)) with (sint.nat num_added + 1)%nat by word.
  iFrame. iSplitR; first word.
  iIntros "[? ?]". iFrame. by iApply "HimpliesP".
Qed.

Lemma wp_WaitGroup__Done P wg :
  {{{ is_pkg_init sync ∗
      "Ha" ∷ own_Done wg P ∗
      "HP" ∷ P
  }}}
    wg @! (go.PointerType sync.WaitGroup) @! "Done" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start_folded as "Hpre". iNamed "Hpre". iNamed "Ha". iNamed "Hinv".
  wp_apply (wp_WaitGroup__Done with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
  iNamedSuffix "Hi" "_inv". iExists _; iFrame.
  iCombine "Hdone_tok Hdone_toks_inv" as "Hdone_toks_inv". simpl.
  iCombine "Haprop Hdone_aprop_inv" as "Hdone_aprop_inv".
  iCombine "Hadded_inv Hdone_toks_inv" gives %Hle.
  iSplitR; first word. iIntros "Hwg_ctr_inv".
  iMod "Hmask". iCombineNamed "*_inv" as "Hi". iMod ("Hclose" with "[Hi HP]").
  { iNamed "Hi". iFrame "Hwg_ctr_inv". iFrame "Hdone_aprop_inv".
    (* FIXME: iFrame seems to frame [?P] in the goal with whatever prop it sees.. *)
    iFrame "Hdone_toks_inv". iFrame "Hadded_inv". iFrame. word. }
  iModIntro. by iApply "HΦ".
Qed.

Lemma wp_WaitGroup__Wait P n wg :
  {{{ is_pkg_init sync ∗ "Ha" ∷ own_Adder wg n P }}}
    wg @! (go.PointerType sync.WaitGroup) @! "Wait" #()
  {{{ RET #(); ▷ P ∗ own_Adder wg (W32 0) True }}}.
Proof.
  wp_start_folded as "Hpre". iApply wp_fupd. iNamed "Hpre". iNamed "Ha". iNamed "Hinv".
  iApply fupd_wp.
  iMod fupd_mask_subseteq as "Hmask"; last iMod (alloc_wait_token with "[$] Hno_waiters") as "[Hwaiter Htok]".
  { solve_ndisj. } { word. } iMod "Hmask" as "_". iModIntro.
  wp_apply (wp_WaitGroup__Wait with "[$]").
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hmask". iNext.
  iNamedSuffix "Hi" "_inv". iExists _; iFrame. iIntros "%Hctr_zero Hwg_ctr_inv".
  assert (ctr = W32 0) as -> by word.
  assert (added = done) as -> by word.
  iCombine "Hadded Hadded_inv" gives %[_ ->].
  iCombine "Hdone_aprop_inv Haprop" gives "Heq".
  iMod (own_aprop_auth_reset with "[$] [$]") as "Haprop".
  iCombine "Hadded Hadded_inv" as "Hadded".
  iMod (own_tok_auth_sub done with "[$] [$]") as "[Hadded Hadded_inv]".
  rewrite Nat.sub_diag. iMod "Hmask" as "_".
  iRename "Hdone_P_inv" into "Hdone_P".
  iDestruct own_aprop_frag_0 as "-#Hdone_aprop_inv".
  iMod own_toks_0 as "Hdone_toks_inv". iCombineNamed "*_inv" as "Hi".
  iMod ("Hclose" with "[Hi]").
  { iNamed "Hi". iFrame. word. }
  iModIntro. iIntros "Hwt".
  iMod fupd_mask_subseteq as "Hmask"; last iMod (dealloc_wait_token with "[$] [$] [$]") as "H".
  { solve_ndisj. }
  { word. }
  iMod "Hmask" as "_". iModIntro. iApply "HΦ". iFrame.
  iDestruct "Heq" as "[Heq _]". iFrame "#". iSplitL; last word.
  iApply "HimpliesP". iApply "Heq". done.
Qed.

Lemma own_Adder_wand P' wg n P :
  (P -∗ P') -∗
  own_Adder wg n P -∗
  own_Adder wg n P'.
Proof.
  iIntros "Hwand". iNamed 1. iFrame "∗#%". iIntros "?".
  iApply "Hwand". iApply "HimpliesP". done.
Qed.

End waitgroup_join_idiom.
End join.
