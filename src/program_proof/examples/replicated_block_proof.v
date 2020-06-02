From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang Require Import crash_modality.
From Perennial.algebra Require Import deletable_heap.

From Goose.github_com.mit_pdos.perennial_examples Require Import replicated_block.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import proof_prelude.

Module rblock.
  Definition t := Block.
End rblock.

Section goose.
  Context `{!heapG Σ}.
  Context `{!lockG Σ}.

  Let N := nroot.@"replicated_block".
  Context (P: rblock.t → iProp Σ).

  Implicit Types (addr: u64) (σ: rblock.t) (γ: gname).

  (* TODO: no longer needed, now that we say the second block is at word.add
  addr 1 *)
  Definition addr_wf (addr: u64) := int.val addr+1 < 2^64.
  Hint Unfold addr_wf : word.

  Definition rblock_linv addr σ : iProp Σ :=
    ("%Haddr_wf" ∷ ⌜addr_wf addr⌝ ∗
     "Hprimary" ∷ int.val addr d↦ σ ∗
     "Hbackup" ∷ int.val (word.add addr 1) d↦ σ)%I.

  Definition rblock_cinv addr σ :=
    ("%Haddr_wf" ∷ ⌜addr_wf addr⌝ ∗
     "Hprimary" ∷ int.val addr d↦ σ ∗
     "Hbackup" ∷ ∃ b0, int.val (word.add addr 1) d↦ b0)%I.

  Instance rblock_crash addr σ :
    IntoCrash (rblock_linv addr σ) (λ _, rblock_cinv addr σ).
  Proof.
    rewrite /IntoCrash.
    iNamed 1.
    rewrite /rblock_cinv.
    iFrame "% Hprimary".
    iIntros (???) "?".
    iExists _; iFrame.
  Qed.

  Definition is_rblock (γ: gname) (l: loc) addr : iProp Σ :=
    ∃ (d_ref m_ref: loc),
      "#d" ∷ readonly (l ↦[RepBlock.S :: "d"] #d_ref) ∗
      "#addr" ∷ readonly (l ↦[RepBlock.S :: "addr"] #addr) ∗
      "#m" ∷ readonly (l ↦[RepBlock.S :: "m"] #m_ref) ∗
      "#Hlock" ∷ is_lock N γ #m_ref (∃ σ, "Hlkinv" ∷ rblock_linv addr σ ∗ "HP" ∷ P σ).

  Definition block0: Block :=
    list_to_vec (replicate (Z.to_nat 4096) (U8 0)).

  Theorem init_zero_cinv addr :
    addr_wf addr →
    int.val addr d↦ block0 ∗ int.val (word.add addr 1) d↦ block0 -∗
    rblock_cinv addr block0.
  Proof.
    iIntros (Haddr_wf) "(Hp&Hb)".
    iFrame "%".
    iSplitL "Hp".
    - iExact "Hp".
    - iExists block0; iExact "Hb".
  Qed.

  Theorem wp_Open (d_ref: loc) addr σ :
    int.val addr + 1 < 2^64 →
    {{{ rblock_cinv addr σ ∗ P σ }}}
      Open #d_ref #addr
    {{{ γ (l:loc), RET #l; is_rblock γ l addr }}}.
  Proof.
    iIntros (Hbound Φ) "(Hinv&HP) HΦ"; iNamed "Hinv".
    wp_call.
    wp_apply (wp_Read with "Hprimary").
    iIntros (s) "(Hprimary&Hb)".
    iDestruct (is_slice_to_small with "Hb") as "Hb".
    wp_apply (wp_Write with "[Hbackup Hb]").
    { iDeexHyp "Hbackup".
      iExists _; iFrame. }
    iIntros "(Hbackup&_)".
    wp_apply wp_new_free_lock.
    iIntros (γ m_ref) "Hfree_lock".
    rewrite -wp_fupd.
    wp_apply wp_allocStruct; auto.
    iIntros (l) "Hrb".
    iDestruct (struct_fields_split with "Hrb") as "(d&addr&m&_)".
    iMod (alloc_lock N ⊤ _ _ (∃ σ, rblock_linv addr σ ∗ P σ)%I
            with "Hfree_lock [Hprimary Hbackup HP]") as "Hlock".
    { iExists _; iFrame "% ∗". }
    iMod (readonly_alloc_1 with "d") as "d".
    iMod (readonly_alloc_1 with "addr") as "addr".
    iMod (readonly_alloc_1 with "m") as "m".
    iModIntro.
    iApply "HΦ".
    iExists _, _; iFrame.
  Qed.

  Theorem wp_RepBlock__Read (Q: Block → iProp Σ) γ l addr (primary: bool) :
    {{{ "Hrb" ∷ is_rblock γ l addr ∗
        "Hfupd" ∷ (∀ σ, P σ ={⊤}=∗ P σ ∗ Q σ) }}}
      RepBlock__Read #l #primary
    {{{ s b, RET (slice_val s); is_block s 1 b ∗ Q b }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
    iNamed "Hrb".
    wp_call.
    wp_loadField.
    wp_apply (acquire_spec with "Hlock").
    iIntros "(His_locked&Hlk)"; iNamed "Hlk".
    wp_pures.
  Admitted.

  Theorem wp_RepBlock__Write (Q: iProp Σ) γ l addr (s: Slice.t) q (b: Block) :
    {{{ "Hrb" ∷ is_rblock γ l addr ∗
        "Hb" ∷ is_block s q b ∗
        "Hfupd" ∷ (∀ σ σ', P σ ={⊤}=∗ P σ' ∗ Q) }}}
      RepBlock__Write #l (slice_val s)
    {{{ RET #(); Q }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
    iNamed "Hrb".
    wp_call.
    wp_loadField.
    wp_apply (acquire_spec with "Hlock").
    iIntros "(His_locked&Hlk)"; iNamed "Hlk".
    wp_pures.
    iNamed "Hlkinv".
    wp_loadField.
    wp_apply (wp_Write_fupd ⊤ (int.val addr d↦ b ∗ P b ∗ Q) with "[Hb Hprimary Hfupd HP]").
    { iFrame "Hb".
      iMod ("Hfupd" with "HP") as "[$ $]".
      iExists _; iFrame.
      iIntros "!> !> Hp".
      by iFrame. }
    iIntros "(Hb&Hprimary&HP&HQ)".
    wp_loadField.
    wp_apply (wp_Write with "[Hb Hbackup]").
    { iExists _; iFrame. }
    iIntros "(Hbackup&Hb)".
    wp_loadField.
    wp_apply (release_spec with "[$Hlock $His_locked HP Hprimary Hbackup]").
    { iExists _; iFrame "% ∗". }
    iApply ("HΦ" with "[$]").
  Qed.

End goose.
