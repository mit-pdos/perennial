From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Export ffi.grove_filesys_axioms.
From Perennial.program_proof.ctrexample Require Import interface.
From Perennial.program_proof Require Import marshal_proof.
From Goose.github_com.mit_pdos.gokv.ctrexample Require Import server.
From Perennial.goose_lang Require Export crash_lock crash_borrow.
From Perennial.program_proof.ctrexample Require Import wpc_proofmode.

Section server_proof.

Context `{!heapGS Σ}.
Context `{!filesysG Σ}.
Context `{!inG Σ mono_natUR}.
Context `{stagedG Σ}.

Definition ctrname := "ctr".

Definition own_CtrServer_durable (c:u64) : iProp Σ :=
  ctrname f↦ [] ∗ ⌜c = U64 0⌝ ∨ (∃ l, ctrname f↦ l ∗ ⌜has_encoding l [EncUInt64 c]⌝)
.

Definition own_CtrServer_ghost γ (c:u64) : iProp Σ :=
  counter_own γ (int.nat c)
.

Definition own_CtrServer (s:loc) (c:u64) : iProp Σ :=
  "Hval" ∷ s ↦[CtrServer :: "val"] #c ∗
  "Hfilename" ∷ s ↦[CtrServer :: "filename"] #(str ctrname)
.

Definition ctrServerN := nroot .@ "ctrserver".

Definition is_CtrServer γ (s:loc) : iProp Σ :=
  ∃ mu,
  "#Hmu" ∷ readonly (s ↦[CtrServer :: "mu"] mu) ∗
  "#HmuInv" ∷ is_crash_lock ctrServerN mu
  (∃ c, own_CtrServer_ghost γ c ∗
        own_CtrServer_durable c ∗
        own_CtrServer s c
  )
  (|={⊤}=> ∃ c, own_CtrServer_ghost γ c ∗
        own_CtrServer_durable c)
.

Lemma wpc_CtrServer__MakeDurable γ (s:loc) c c' {stk E}:
  {{{
       own_CtrServer_ghost γ c ∗ own_CtrServer_durable c ∗ own_CtrServer s c'
                           ∗ (own_CtrServer_ghost γ c ={E}=∗ own_CtrServer_ghost γ c')
  }}}
    CtrServer__MakeDurable #s @ stk ; E
  {{{
       RET #(); own_CtrServer_ghost γ c' ∗ own_CtrServer_durable c' ∗ own_CtrServer s c'
  }}}
  {{{
       (* FIXME: can I have this fupd here? I actually only need bupd, but want
       to see if fupd will work *)
       |={E}=> ∃ c'', own_CtrServer_ghost γ c'' ∗ own_CtrServer_durable c''
  }}}.
Proof.
  iIntros (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "(Hghost & Hdur & Hvol & Hfupd)".
  unfold CtrServer__MakeDurable.
  wpc_pures.
  { iLeft in "HΦ". iApply "HΦ". iModIntro. iExists _; iFrame. }
  iCache with "Hghost Hdur HΦ".
  {
    iLeft in "HΦ".
    iApply "HΦ".
    iModIntro.
    iExists _; iFrame.
  }

  wpc_wpapply (wp_new_enc).
  iIntros (enc) "Henc".
  iNamed 1.
  wpc_pures.
  iNamed "Hvol".
  wpc_loadField.
  wpc_wpapply (wp_Enc__PutInt with "[$Henc]").
  { done. }
  iIntros "Henc".
  iNamed 1.
  wpc_pures.

  wpc_wpapply (wp_Enc__Finish with "[$Henc]").
  iIntros (sl data) "(%Henc & %Hlen & Hslice)".
  iNamed 1.
  wpc_loadField.

  iDestruct "Hdur" as "[Hdur | Hdur]".
  { (* Case 1: initially empty file *)
    iDestruct "Hdur" as "[Hdur %Hc]".
    wpc_apply (wpc_Write with "[Hdur Hslice]").
    {
      iFrame.
    }
    iSplit.
    { (* crash-condition of Write implies our crash condition *)
      iLeft in "HΦ".
      iIntros "Hcrash".
      iApply "HΦ".
      iDestruct "Hcrash" as "[Hdur|Hdur]".
      { (* write didn't go through *)
        iExists _. iFrame.
        iLeft.
        iFrame.
        done.
      }
      { (* write went through *)
        iExists _.
        iSplitR "Hdur"; last first.
        {
          iRight.
          iExists _; iFrame.
          done.
        }
        by iApply "Hfupd".
      }
    }
    { (* proof after Write completes *)
      iNext.
      iIntros "[Hdur Hslice]".
      iMod ("Hfupd" with "Hghost") as "Hghost".
      iCache with "Hdur Hghost HΦ".
      {
        iLeft in "HΦ".
        iApply "HΦ".
        iModIntro.
        iExists _; iFrame.
        iRight.
        iExists _; iFrame.
        done.
      }
      wpc_pures.
      iModIntro.
      iRight in "HΦ".
      iApply "HΦ".
      iFrame.
      iRight.
      iExists _; iFrame.
      done.
    }
  }
  { (* Case 2: old file was non-empty *)
    (* FIXME: shouldn't have to make this a separate case; would end up
    copy/pasting the above proof to this branch *)
    admit.
  }
Admitted.

Lemma wp_CtrServer__FetchAndIncrement γ (s:loc) :
  {{{
       is_CtrServer γ s
  }}}
    CtrServer__FetchAndIncrement #s
  {{{
       (x:u64), RET #x; True
  }}}
.
Proof.
  iIntros (Φ) "#Hpre HΦ".
  wp_lam.
  iNamed "Hpre".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  { done. }
  iIntros "Hres".
  wp_pures.
  wp_apply wpc_wp.

  wpc_apply (use_crash_locked with "Hres").
  { done. }
  iSplit.
  { by instantiate (1:=True%I). }
  iIntros "H".
  iDestruct "H" as (c) "(Hghost&Hdur&Hvol)".

  iNamed "Hvol".
  iCache with "Hghost Hdur".
  {
    iSplitL ""; first done.
    iModIntro.
    iExists c; iFrame.
  }

  wpc_loadField.
  wpc_pures.
  wpc_loadField.
  wpc_pures.
  wpc_storeField.
  wpc_pures.
  wpc_apply (wpc_CtrServer__MakeDurable with "[$Hghost $Hdur $Hval $Hfilename]").
  {
    iIntros "Hghost".
    iApply (own_update with "Hghost").
    apply mono_nat_update.
    (* FIXME: need no-overflow assumption *)
    admit.
  }
  iSplit.
  { (* crash-condition of MakeDurable ==> our crash condition *)
    eauto.
  }
  iNext.
  iIntros "(Hghost & Hdur & Hvol)".
  iCache with "Hghost Hdur".
  { iSplitL ""; first done. iModIntro. iExists _; iFrame. }
  wpc_pures.
  wpc_loadField.

  wpc_apply (wpc_crash_borrow_inits _ _ _ _
  (∃ c, own_CtrServer_ghost γ c ∗ own_CtrServer_durable c ∗ own_CtrServer s c)
                                    (|={⊤}=> ∃ c, own_CtrServer_ghost γ c ∗ own_CtrServer_durable c)
               with "[] [Hvol Hdur Hghost] []").
  { admit. (* FIXME: what is this about? *) }
  {
    iExists _; iFrame.
  }
  {
    iModIntro.
    iIntros "H".
    iModIntro.
    iDestruct "H" as (c2) "(H & H2 & _)".
    iExists _; iFrame.
  }
  iIntros "Hres".

  iApply (wpc_crash_mono _ _ _ _ _ (True) with "[]").
  {
    iIntros.
    iSplitL ""; first done.
    iFrame.
  }
  iApply wp_wpc.
  wp_apply (release_spec with "[Hres]").
  { done. }
  { unfold crash_locked.
    iFrame.
    unfold is_crash_lock.
    iFrame "HmuInv".
    (* FIXME: lost the lock.locked because of use_crash_locked binding too far *)
    admit.
  }

  wp_pures.
  iSplitL "HΦ".
  {
    iModIntro. iIntros.
    admit.
  }
Admitted.

End server_proof.
