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

Section heap.
Context `{!buftxnG Σ}.
Context `{!ghost_varG Σ (gmap u64 (list u8))}.
Context `{!mapG Σ u64 (list u8)}.
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
  replace 1024%Z with (Z.of_nat $ length (replicate (int.nat 1024%Z) (U8 0))).
  2: { rewrite replicate_length. word. }

  wp_apply (wp_NFSPROC3_WRITE with "[$Hfs $Hfh Hs]").
  { iFrame "Hs".
    iSplit; first by len.
    admit. (* HOCAP fupd *) }
Admitted.

Theorem wpc_RecoverExample γ (d : loc) dinit logm klevel :
  {{{
    is_txn_durable γ dinit logm
  }}}
    RecoverExample #d @ S klevel; ⊤
  {{{ RET #(); True }}}
  {{{ True }}}.
Proof.
  iIntros (Φ Φc) "Htxndurable HΦ".
  rewrite /RecoverExample.
  wpc_pures.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iApply "HΦc". done. }

  wpc_apply (wpc_MkTxn with "Htxndurable").

  iSplit.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iIntros "H".
    iDestruct "H" as (γ' logm') "(%Hkinds & Htxndurable)".
    iApply "HΦc". done. }

  iModIntro.
  iIntros (γ' l) "(#Histxn & #Htxnsys & Hcfupdcancel & Htxncrash)".

  wpc_pures.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iApply "HΦc". done. }

  wpc_apply wpc_MkLockMap.
  { (* where to get old predicates? probably [Hlmcrash] from below.. *) admit. }

  iSplit.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iIntros "H".
    iApply "HΦc". done. }

  iModIntro.
  iIntros (lm ghs) "[#Hlm Hlmcrash]".

  wpc_pures.
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. iApply "HΦc". done. }

  
  admit.
Admitted.

Print Assumptions wpc_RecoverExample.

End heap.
