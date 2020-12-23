From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Perennial.algebra Require Import deletable_heap liftable auth_map.
From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude.

From Goose.github_com.mit_pdos.goose_nfsd Require Import simple.
From Perennial.program_proof Require Import txn.txn_proof marshal_proof addr_proof crash_lockmap_proof addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_proof buftxn.sep_buftxn_recovery_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import disk_lib.
From Perennial.Helpers Require Import NamedProps Map List range_set.
From Perennial.algebra Require Import log_heap.
From Perennial.program_logic Require Import spec_assert.
From Perennial.goose_lang.lib Require Import slice.typed_slice into_val.
From Perennial.program_proof.simple Require Import spec invariant proofs.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.goose_lang Require wpr_lifting.

Section heap.
Context `{!heapG Σ}.
Context `{!gen_heapPreG u64 bool Σ}.
Context `{!simpleG Σ}.
Implicit Types (stk:stuckness) (E: coPset).

Definition P (s : SimpleNFS.State) : iProp Σ :=
  True.

Theorem wp_exampleWorker (nfs : loc) (inum : u64) γ dinit :
  {{{ is_fs P γ nfs dinit }}}
    exampleWorker #nfs #inum
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "#Hfs HΦ".
  wp_call.
  wp_apply (wp_NewSlice (V:=u8)).
  iIntros (s) "Hs".

  wp_apply wp_Fh__MakeFh3.
  iIntros (fh0) "Hfh".
  wp_apply (wp_NFSPROC3_GETATTR with "[$Hfs $Hfh]").
  { iIntros (σ σ' r E) "%Hrel HP".
    iModIntro. iSplit; done. }
  iIntros (v0) "Hv0".

  wp_apply wp_Fh__MakeFh3.
  iIntros (fh1) "Hfh".
  wp_apply (wp_NFSPROC3_READ with "[$Hfs $Hfh]").
  { iIntros (σ σ' r E) "%Hrel HP".
    iModIntro. iSplit; done. }
  iIntros (v1) "Hv1".

  wp_apply wp_Fh__MakeFh3.
  iIntros (fh2) "Hfh".
  wp_apply (wp_NFSPROC3_WRITE with "[$Hfs $Hfh $Hs]").
  { rewrite !replicate_length. iSplit.
    { iPureIntro. word. }
    iModIntro.
    iIntros (σ σ' r E) "%Hrel HP".
    iModIntro. iSplit; done. }
  iIntros (v2) "Hv2".

  wp_pures.
  iApply "HΦ". done.
Qed.

Theorem wpc_RecoverExample γ γsrc (d : loc) dinit logm :
  {{{
    is_txn_durable γ dinit logm ∗
    is_source P γsrc ∗
    [∗ set] a ∈ covered_inodes, is_inode_stable γsrc γ a
  }}}
    RecoverExample #d @ 10; ⊤
  {{{ RET #(); True }}}
  {{{
    ∃ γ' γsrc' logm',
    is_txn_durable γ' dinit logm' ∗
    is_source P γsrc' ∗
    [∗ set] a ∈ covered_inodes, is_inode_stable γsrc' γ' a
  }}}.
Proof using All.
  iIntros (Φ Φc) "(Htxndurable & Hsrc & Hstable) HΦ".
  rewrite /RecoverExample.
  wpc_pures.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iApply "HΦc".
    iExists _, _, _. iFrame. }

  iApply wpc_cfupd.
  wpc_apply (wpc_Recover P P with "[$Htxndurable $Hsrc $Hstable]").
  { eauto. }
  iSplit.
  { iLeft in "HΦ". iIntros "!> H". iDestruct "H" as (???) "(H1&>H2&H3)".
    iModIntro. iApply "HΦ". iExists _, _, _. iFrame.
  }
  iNext. iIntros (??) "(#Hfs&Hcancel)".
  iApply wp_wpc_frame'.
  iSplitL "Hcancel HΦ".
  { iSplit.
    { iDestruct "HΦ" as "[HΦc _]". iModIntro.
      iMod "Hcancel" as (???) "(?&>?&?)".
      iModIntro. iApply "HΦc".
      iExists _, _, _. iFrame. }
    { iRight in "HΦ". iExact "HΦ". }
  }

  wp_pures.
  wp_apply wp_fork.
  { wp_apply wp_exampleWorker. { iExact "Hfs". } done. }

  wp_apply wp_fork.
  { wp_apply wp_exampleWorker. { iExact "Hfs". } done. }

  wp_apply wp_fork.
  { wp_apply wp_exampleWorker. { iExact "Hfs". } done. }

  iIntros "HΦ". iApply "HΦ". done.
Qed.

End heap.

Import wpr_lifting.

Section recov.
  Context `{!heapG Σ}.
  Context `{!gen_heapPreG u64 bool Σ}.
  Context `{!simpleG Σ}.

  (* Just a simple example of using idempotence *)
  Theorem wpr_RecoverExample (d: loc) γ γsrc dinit logm:
    is_txn_durable γ dinit logm -∗
    is_source P γsrc -∗
    ([∗ set] a ∈ covered_inodes, is_inode_stable γsrc γ a) -∗
    wpr NotStuck 10 ⊤
        (RecoverExample #d)
        (RecoverExample #d)
        (λ _, True%I)
        (λ _, True%I)
        (λ _ _, True%I).
  Proof using All.
    iIntros "Hdurable Hsource Hinodes".
    iApply (idempotence_wpr NotStuck 10 ⊤ _ _ (λ _, True)%I (λ _, True)%I (λ _ _, True)%I
                            (λ _, ∃ γ' γsrc' logm',
                                is_txn_durable γ' dinit logm' ∗
                                is_source P γsrc' ∗
                                [∗ set] a ∈ covered_inodes, is_inode_stable γsrc' γ' a)%I
                            with "[-] []").
    { wpc_apply (wpc_RecoverExample with "[-]").
      { iFrame "Hdurable". iFrame "Hsource". iExact "Hinodes". }
      eauto. }
    iModIntro.
    iIntros (?????) "H".
    iDestruct "H" as (???) "(Hdurable&Hsource&Hinodes)".
    iNext. iDestruct (is_source_into_crash P (λ _, P) with "[] [$]") as "Hsource".
    { eauto. }
    iCrash. iIntros "_". iSplit; first eauto.
    { wpc_apply (wpc_RecoverExample with "[-]").
      { iFrame "Hdurable". iFrame "Hsource". iExact "Hinodes". }
      eauto. }
  Qed.

  Print Assumptions wpr_RecoverExample.
End recov.
