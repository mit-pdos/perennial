From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.grove_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Export ffi.grove_filesys_axioms.
From Perennial.program_proof.ctrexample Require Import interface.
From Perennial.program_proof Require Import marshal_proof.
From Goose.github_com.mit_pdos.gokv.ctrexample Require Import server.
From Perennial.goose_lang Require Export crash_lock.
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
  (∃ c, own_CtrServer_ghost γ c ∗
        own_CtrServer_durable c)
.

Lemma wpc_CtrServer__MakeDurable γ (s:loc) c c' {stuck P}:
  {{{
       own_CtrServer_ghost γ c ∗ own_CtrServer_durable c ∗ own_CtrServer s c'
  }}}
    CtrServer__MakeDurable #s @ stuck ; P
  {{{
       RET #(); own_CtrServer_ghost γ c' ∗ own_CtrServer_durable c' ∗ own_CtrServer s c'
  }}}
  {{{
       ∃ c'', own_CtrServer_ghost γ c'' ∗ own_CtrServer_durable c''
  }}}.
Proof.
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
    iExists c; iFrame.
  }

  wpc_loadField.
  wpc_pures.
  wpc_loadField.
  wpc_pures.
  (* FIXME: need no-overflow assumption *)
  wpc_storeField.
  wpc_pures.
  wpc_apply (wpc_CtrServer__MakeDurable with "[$Hghost $Hdur $Hval $Hfilename]").
  iSplit.
  { (* crash-condition of MakeDurable ==> our crash condition *)
    eauto.
  }
  iNext.
  iIntros "(Hghost & Hdur & Hvol)".
  iCache with "Hghost Hdur".
  { iSplitL ""; first done. iExists _; iFrame. }
  wpc_pures.
  wpc_loadField.
  (* wpc_apply (release_spec with "[]"). *)
Admitted.

End server_proof.
