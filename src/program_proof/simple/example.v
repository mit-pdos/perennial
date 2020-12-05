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

Section stable.
Context `{!buftxnG Σ}.
Context `{!gen_heapPreG u64 bool Σ}.
Context `{!ghost_varG Σ (gmap u64 (list u8))}.
Context `{!mapG Σ u64 (list u8)}.

Global Instance is_inode_stable_set_stable γsrc γ':
    IntoCrash ([∗ set] a ∈ covered_inodes, is_inode_stable γsrc γ' a)
              (λ _, ([∗ set] a ∈ covered_inodes, is_inode_stable γsrc γ' a))%I.
Proof. rewrite /IntoCrash. iApply post_crash_nodep. Qed.

Global Instance is_txn_durable_stable γ dinit logm:
    IntoCrash (is_txn_durable γ dinit logm) (λ _, is_txn_durable γ dinit logm).
Proof.
  rewrite /IntoCrash. iNamed 1.
  iDestruct (post_crash_nodep with "Hlogm") as "Hlogm".
  iDestruct (post_crash_nodep with "Hasync_ctx") as "Hasync_ctx".
  iCrash. rewrite /is_txn_durable. iFrame "Hlogm Hasync_ctx".
Admitted.

End stable.

Section heap.
Context `{!buftxnG Σ}.
Context `{!gen_heapPreG u64 bool Σ}.
Context `{!ghost_varG Σ (gmap u64 (list u8))}.
Context `{!mapG Σ u64 (list u8)}.
Implicit Types (stk:stuckness) (E: coPset).

Definition P (s : SimpleNFS.State) : iProp Σ :=
  True.

Theorem wp_exampleWorker (nfs : loc) (inum : u64) γ dinit :
  {{{ is_fs P γ nfs dinit }}}
    exampleWorker #nfs #inum
  {{{ RET #(); True }}}.
Proof using ghost_varG0.
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
    inv N (is_source P γsrc) ∗
    [∗ set] a ∈ covered_inodes, is_inode_stable γsrc γ a
  }}}
    RecoverExample #d @ 10; ⊤
  {{{ RET #(); True }}}
  {{{
    ∃ γ' logm',
    is_txn_durable γ' dinit logm' ∗
    [∗ set] a ∈ covered_inodes, is_inode_stable γsrc γ' a
  }}}.
Proof using buftxnG0 gen_heapPreG0 ghost_varG0 mapG0 Σ.
  iIntros (Φ Φc) "(Htxndurable & #Hsrc & Hstable) HΦ".
  rewrite /RecoverExample.
  wpc_pures.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iApply "HΦc".
    iExists _, _. iFrame. }

  iApply wpc_cfupd.
  wpc_apply (wpc_MkTxn Nbuftxn with "Htxndurable").
  { solve_ndisj. }
  { solve_ndisj. }

  iSplit.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iIntros "H".
    iDestruct "H" as (γ' logm') "(%Hkinds & Htxndurable)".
    iDestruct "Htxndurable" as "(Hdurable&[%Heq|#Hexch])".
    { subst. iModIntro. iApply "HΦc". iExists _, _. iFrame. }
    iMod (big_sepS_impl_cfupd with "Hstable []") as "Hcrash".
    { iModIntro. iIntros (x Hx) "H".
      iApply (is_inode_stable_crash with "[$] H").
    }
    iModIntro.
    iApply "HΦc".
    iExists _, _. iFrame.
  }

  iModIntro.
  iIntros (γ' l) "(#Histxn & #Htxnsys & Hcfupdcancel & #Htxncrash)".

  wpc_pures.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro.
    iMod (big_sepS_impl_cfupd with "Hstable []") as "Hcrash".
    { iModIntro. iIntros (x Hx) "H".
      iMod (is_inode_stable_crash with "Htxncrash H") as "H".
      iModIntro. iExact "H". }
    iMod "Hcfupdcancel" as ">Hcfupdcancel".
    iModIntro.
    iApply "HΦc".
    iDestruct "Hcfupdcancel" as (?) "H".
    iExists _, _.
    iFrame "Hcrash H".
  }

  wpc_apply (wpc_MkLockMap _ covered_inodes (is_inode_stable γsrc γ) (is_inode_stable γsrc γ') with "[Hstable]").
  { iApply (big_sepS_impl with "Hstable").
    iModIntro.
    iIntros (a Ha) "H". iFrame.
    iModIntro. iIntros ">Hstable".
    iMod (is_inode_stable_crash with "Htxncrash Hstable") as "Hstable".
    iModIntro. done. }

  iSplit.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iIntros "H".
    rewrite -big_sepS_later.
    iDestruct "H" as ">H".
    iMod "Hcfupdcancel" as ">Hcfupdcancel".
    iDestruct "Hcfupdcancel" as (?) "Hcfupdcancel".
    iModIntro.
    iApply "HΦc".
    iExists _, _.
    iFrame.
  }

  iModIntro.
  iIntros (lm ghs) "[#Hlm Hlmcrash]".

  iApply wp_wpc_frame'.
  iSplitL "Hlmcrash Hcfupdcancel HΦ".
  { iSplit.
    { iDestruct "HΦ" as "[HΦc _]". iModIntro.
      rewrite -big_sepS_later.
      iMod "Hlmcrash" as ">Hlmcrash". iMod "Hcfupdcancel" as ">Hcfupdcancel".
      iModIntro. iApply "HΦc". iDestruct "Hcfupdcancel" as (?) "?". 
      iExists _, _. iFrame. }
    { iDestruct "HΦ" as "[_ HΦ]". iExact "HΦ". } }

  wp_apply wp_allocStruct; first by eauto.
  iIntros (nfs) "Hnfs".

  iDestruct (struct_fields_split with "Hnfs") as "Hnfs". iNamed "Hnfs".
  iMod (readonly_alloc_1 with "t") as "#Ht".
  iMod (readonly_alloc_1 with "l") as "#Hl".

  iAssert (is_fs P (Build_simple_names γ γ' γsrc ghs) nfs dinit) with "[]" as "Hfs".
  { iExists _, _.
    iFrame "Ht Hl Histxn Htxnsys Htxncrash Hsrc Hlm".
  }

  wp_apply wp_fork.
  { wp_apply wp_exampleWorker. { iExact "Hfs". } done. }

  wp_apply wp_fork.
  { wp_apply wp_exampleWorker. { iExact "Hfs". } done. }

  wp_apply wp_fork.
  { wp_apply wp_exampleWorker. { iExact "Hfs". } done. }

  iIntros "HΦ". iApply "HΦ". done.
Qed.

Print Assumptions wpc_RecoverExample.

End heap.
