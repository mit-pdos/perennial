From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang Require Import crash_modality.
From Perennial.algebra Require Import deletable_heap.

From Goose.github_com.mit_pdos.perennial_examples Require Import replicated_block.
From Perennial.goose_lang.lib Require Import lock.crash_lock.
From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import proof_prelude.

(** * Replicated block example

    Replicates single-block writes across two underlying disk blocks, and
    supports read from either the "primary" or "backup" block.

    On crash the blocks may disagree. In that case the recovery procedure copies
    from the primary to restore synchronization.
 *)

(* the abstract state of the replicated block is  *)
Module rblock.
  Definition t := Block.
End rblock.

Section goose.
  Context `{!heapG Σ}.
  Context `{!lockG Σ}.
  Context `{!crashG Σ}.
  Context `{!stagedG Σ}.

  Implicit Types (l:loc) (addr: u64) (σ: rblock.t) (γ: gname).

  (* the replicated block has a stronger lock invariant [rblock_linv] that holds
  when the lock is free as well as a weaker crash invariant [rblock_cinv] that
  holds at all intermediate points *)
  Definition rblock_linv addr σ : iProp Σ :=
    ("Hprimary" ∷ int.val addr d↦ σ ∗
     "Hbackup" ∷ int.val (word.add addr 1) d↦ σ)%I.

  Definition rblock_cinv addr σ :=
    ("Hprimary" ∷ int.val addr d↦ σ ∗
     "Hbackup" ∷ ∃ b0, int.val (word.add addr 1) d↦ b0)%I.
  (* Let eauto unfold this *)
  Local Hint Extern 0 (environments.envs_entails _ (rblock_cinv _ _)) => unfold rblock_cinv : core.

  Theorem rblock_linv_to_cinv addr σ :
    rblock_linv addr σ -∗ rblock_cinv addr σ.
  Proof.
    iNamed 1.
    iFrame "Hprimary".
    iExists _; iFrame.
  Qed.

  Instance rblock_crash addr σ :
    IntoCrash (rblock_linv addr σ) (λ _, rblock_cinv addr σ).
  Proof.
    rewrite /IntoCrash.
    rewrite rblock_linv_to_cinv.
    iIntros "$".
    auto.
  Qed.

  (** the abstraction relation for the replicated block is written in HOCAP
  style, by quantifying over an arbitrary caller-specified predicate [P] of the
  block's state. *)
  Let N := nroot.@"replicated_block".
  Context (P: rblock.t → iProp Σ).

  Definition is_rblock (γ: gname) (k': nat) (l: loc) addr : iProp Σ :=
    ∃ (d_ref m_ref: loc),
      (* reflect coq values in program data structure *)
      "#d" ∷ readonly (l ↦[RepBlock.S :: "d"] #d_ref) ∗
      "#addr" ∷ readonly (l ↦[RepBlock.S :: "addr"] #addr) ∗
      "#m" ∷ readonly (l ↦[RepBlock.S :: "m"] #m_ref) ∗
      (* lock protocol *)
      "#Hlock" ∷ is_crash_lock N N (LVL k') γ #m_ref
        (∃ σ, "Hlkinv" ∷ rblock_linv addr σ ∗ "HP" ∷ P σ)
        (∃ σ, "Hclkinv" ∷ rblock_cinv addr σ ∗ "HP" ∷ P σ)
  .

  Global Instance is_rblock_Persistent γ k' l addr :
    Persistent (is_rblock γ k' l addr).
  Proof. apply _. Qed.

  Definition block0: Block :=
    list_to_vec (replicate (Z.to_nat 4096) (U8 0)).

  Theorem init_zero_cinv addr :
    int.val addr d↦ block0 ∗ int.val (word.add addr 1) d↦ block0 -∗
    rblock_cinv addr block0.
  Proof.
    iIntros "(Hp&Hb)".
    iSplitL "Hp".
    - iExact "Hp".
    - iExists block0; iExact "Hb".
  Qed.

  (* Open is the replicated block's recovery procedure, which constructs the
  in-memory state as well as recovering the synchronization between primary and
  backup, going from the crash invariant to the lock invariant. *)
  Theorem wpc_Open {k E2} (d_ref: loc) k' addr σ :
    (k' < S k)%nat →
    {{{ rblock_cinv addr σ ∗ P σ }}}
      Open #d_ref #addr @ NotStuck;LVL (S (S k)); ⊤;E2
    {{{ γ (l:loc), RET #l; is_rblock γ k' l addr }}}
    {{{ ∃ σ', rblock_cinv addr σ' ∗ P σ' }}}.
  Proof.
    iIntros (? Φ Φc) "(Hinv&HP) HΦ"; iNamed "Hinv".
    iDeexHyp "Hbackup".
    wpc_call.
    { eauto with iFrame. }
    iCache with "Hprimary Hbackup HP HΦ".
    { crash_case. eauto with iFrame. }
    (* read block content, write it to backup block *)
    wpc_apply (wpc_Read with "Hprimary").
    iSplit; [ | iNext ].
    { iIntros "Hprimary".
      iFromCache. }
    iIntros (s) "(Hprimary&Hb)".
    iDestruct (is_slice_to_small with "Hb") as "Hb".
    wpc_pures.
    wpc_apply (wpc_Write' with "[$Hbackup $Hb]").
    iSplit; [ | iNext ].
    { iIntros "[Hbackup|Hbackup]"; try iFromCache.
      crash_case. eauto with iFrame. }
    iIntros "(Hbackup&_)".
    iCache with "HP HΦ Hprimary Hbackup".
    { crash_case. eauto with iFrame. }

    (* allocate lock *)
    wpc_pures.
    wpc_bind (lock.new _).
    wpc_frame.
    wp_apply wp_new_free_lock.
    iIntros (γ m_ref) "Hfree_lock".
    iNamed 1.

    (* actually initialize the lock *)
    iApply (alloc_crash_lock N N _ k' _ _ _ _ _ _
                             (∃ σ, "Hlkinv" ∷ rblock_linv addr σ ∗ "HP" ∷ P σ)%I
                             (∃ σ, "Hclkinv" ∷ rblock_cinv addr σ ∗ "HP" ∷ P σ)%I
            with "[$Hfree_lock Hprimary Hbackup HP HΦ]").
    { lia. }
    iSplitR.
    { iIntros "!>"; iNamed 1.
      iExists _; iFrame.
      iApply rblock_linv_to_cinv; iFrame. }
    iSplitL "Hprimary Hbackup HP".
    { eauto with iFrame. }
    iIntros "His_crash_lock".

    (* allocate struct *)
    rewrite -wpc_fupd.
    wpc_frame "HΦ".
    { iNamed 1. crash_case. eauto with iFrame. }
    wp_apply wp_allocStruct; auto.
    iIntros (l) "Hrb".
    iNamed 1.

    (* ghost allocation *)
    iDestruct (struct_fields_split with "Hrb") as "(d&addr&m&_)".
    iMod (readonly_alloc_1 with "d") as "d".
    iMod (readonly_alloc_1 with "addr") as "addr".
    iMod (readonly_alloc_1 with "m") as "m".
    iModIntro.
    iApply "HΦ".
    iExists _, _; iFrame.
  Qed.

  (* this is an example of a small helper function which needs only a WP spec
  since the spec does not talk about durable state. *)
  Theorem wp_RepBlock__readAddr addr l (primary: bool) :
    {{{ readonly (l ↦[RepBlock.S :: "addr"] #addr) }}}
      RepBlock__readAddr #l #primary
    {{{ (a: u64), RET #a; ⌜a = addr ∨ a = word.add addr 1⌝ }}}.
  Proof.
    iIntros (Φ) "#addr HΦ".
    wp_call.
    wp_if_destruct.
    - wp_loadField.
      iApply "HΦ"; auto.
    - wp_loadField.
      wp_pures.
      iApply "HΦ"; auto.
  Qed.

  Lemma wpc_RepBlock__Read' {k E2} {k' γ l} addr (primary: bool) :
    (S k < k')%nat →
    ∀ Φ Φc,
        "Hrb" ∷ is_rblock γ k' l addr ∗
        "Hfupd" ∷ (Φc (* crash condition before lin.point *) ∧
                   ▷ (∀ σ, P σ ={⊤ ∖ ↑N}=∗ P σ ∗ ((∀ s, is_block s 1 σ -∗ Φ (slice_val s))
                                                  ∧ Φc (* crash condition after lin.point *)))) -∗
      WPC RepBlock__Read #l #primary @ NotStuck; LVL (S (S k)); ⊤; E2 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (? Φ Φc) "Hpre"; iNamed "Hpre".
    iNamed "Hrb".
    wpc_call.
    { by iLeft in "Hfupd". }
    iCache with "Hfupd".
    { by iLeft in "Hfupd". }
    wpc_frame_seq.
    wp_loadField.
    wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
    iIntros (γlk) "His_locked"; iNamed 1.
    wpc_pures.
    wpc_bind (RepBlock__readAddr _ _); wpc_frame.
    wp_apply (wp_RepBlock__readAddr with "addr").
    iIntros (addr' Haddr'_eq).
    iNamed 1.

    wpc_bind_seq.
    iApply (use_crash_locked with "His_locked"); auto.
    iSplit; first by iFromCache.
    iNamed 1.
    iAssert (int.val addr' d↦ σ ∗
                   (int.val addr' d↦ σ -∗ rblock_linv addr σ))%I
      with "[Hlkinv]" as "(Haddr'&Hlkinv)".
    { iNamed "Hlkinv".
      destruct Haddr'_eq; subst; iFrame; auto. }
    iRight in "Hfupd".
    iMod ("Hfupd" with "HP") as "[HP HQ]".

    wpc_apply (wpc_Read with "Haddr'").
    iSplit; [ | iNext ].
    { iIntros "Hd".
      iSpecialize ("Hlkinv" with "Hd").
      iSplitL "HQ".
      { by iRight in "HQ". }
      iExists _; iFrame.
      iApply rblock_linv_to_cinv; iFrame. }
    iIntros (s) "(Haddr'&Hb)".
    iDestruct (is_slice_to_small with "Hb") as "Hb".
    iSpecialize ("Hlkinv" with "Haddr'").
    iSplitR "HP Hlkinv"; last first.
    (* TODO: why is this the second goal?
       RALF: because use_crash_locked puts [R] to the right. *)
    { iExists _; iFrame. }
    iIntros "His_locked".
    iCache Φc with "HQ".
    { by iRight in "HQ". }
    iSplit; last by iFromCache. (* TODO: why is this the second goal? RALF: because use_crash_locked puts [Φc] to the right. *)
    wpc_pures.
    wpc_frame.

    wp_loadField.
    wp_apply (crash_lock.release_spec with "[$His_locked]"); auto.
    wp_pures.
    iNamed 1.
    iLeft in "HQ".
    iApply "HQ"; iFrame.
  Qed.

  Theorem wpc_RepBlock__Read (Q: Block → iProp Σ) (Qc: iProp Σ) {k E2} {k' γ l} addr (primary: bool) :
    (S k < k')%nat →
    {{{ "Hrb" ∷ is_rblock γ k' l addr ∗
        "HQc" ∷ (∀ σ, Q σ -∗ Qc) ∗ (* crash condition after "linearization point" *)
        "Hfupd" ∷ ((∀ σ, P σ ={⊤ ∖ ↑N}=∗ P σ ∗ Q σ) ∧ Qc (* crash condition before "linearization point" *)) }}}
      RepBlock__Read #l #primary @ NotStuck; LVL (S (S k)); ⊤; E2
    {{{ s b, RET (slice_val s); is_block s 1 b ∗ Q b }}}
    {{{ Qc }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    iApply wpc_RepBlock__Read'; first done.
    iFrame "Hrb".
    iSplit.
    - iRight in "Hfupd". iLeft in "HΦ". iApply "HΦ". done.
    - iNext. iIntros (σ) "HP". iLeft in "Hfupd". iMod ("Hfupd" with "HP") as "[HP HQ]".
      iModIntro. iFrame "HP". iSplit.
      + iIntros (s) "Hblock". iRight in "HΦ". iApply "HΦ". iFrame.
      + iLeft in "HΦ". iApply "HΦ". iApply "HQc". done.
  Qed.

  Theorem wpc_RepBlock__Write (Q: iProp Σ) (Qc: iProp Σ) {k E2} γ l k' addr (s: Slice.t) q (b: Block) :
    (S k < k')%nat →
    {{{ "Hrb" ∷ is_rblock γ k' l addr ∗
        "Hb" ∷ is_block s q b ∗
        "HQc" ∷ (Q -∗ Qc) ∗
        "Hfupd" ∷ ((∀ σ σ', P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q) ∧ Qc) }}}
      RepBlock__Write #l (slice_val s) @ NotStuck; LVL (S (S k)); ⊤; E2
    {{{ RET #(); Q }}}
    {{{ Qc }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    iNamed "Hrb".
    wpc_call.
    { iRight in "Hfupd"; auto. }
    iCache with "HΦ Hfupd".
    { crash_case.
      iRight in "Hfupd"; auto. }
    wpc_frame_seq.
    wp_loadField.
    wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
    iIntros (γlk) "His_locked".
    iNamed 1.

    wpc_pures.
    wpc_bind_seq.
    iApply (use_crash_locked with "His_locked"); auto.
    iSplit; first by iFromCache.
    iNamed 1.
    iNamed "Hlkinv".

    iCache with "HP Hprimary Hbackup HΦ Hfupd".
    { iSplitL "HΦ Hfupd"; first by iFromCache.
      iExists _; iFrame.
      iExists _; iFrame. }

    wpc_call.
    wpc_bind (struct.loadF _ _ _).
    wpc_frame.
    wp_loadField.
    iNamed 1.
    (* This is an interesting example illustrating crash safety - notice that we
    produce [Q] atomically during this Write. This is the only valid simulation
    point in this example, because if we crash the operation has logically
    occurred due to recovery.

    Also note that this is quite different from the Perennial example which
    requires helping due to the possibility of losing the first disk block
    between crash and recovery - the commit cannot happen until recovery
    succesfully synchronizes the disks. *)
    wpc_apply (wpc_Write_fupd (⊤ ∖ ↑N) ("Hprimary" ∷ int.val addr d↦ b ∗
                                        "HP" ∷ P b ∗
                                        "HQ" ∷ Q)
              with "[$Hb Hprimary Hfupd HP]").
    { iSplit; [ iNamedAccu | ].
      iModIntro.
      iExists _; iFrame.
      iNext.
      iIntros "Hda".
      iMod ("Hfupd" with "HP") as "[$ $]".
      iModIntro; auto. }
    iSplit; [ | iNext ].
    { iIntros "Hpost".
      iDestruct "Hpost" as "[Hpost|Hpost]"; iNamed "Hpost"; try iFromCache.
      iSplitL "HΦ HQc HQ".
      - crash_case.
        iApply ("HQc" with "[$]").
      - iExists _; iFrame.
        iExists _; iFrame. }
    iIntros "(Hb&Hpost)"; iNamed "Hpost".
    iCache Φc with "HΦ HQ HQc".
    { crash_case.
      iApply ("HQc" with "[$]"). }
    iCache with "HΦ HQ HQc Hprimary Hbackup HP".
    { iSplitL "HΦ HQc HQ"; first by iFromCache.
      iExists _; iFrame.
      iExists _; iFrame. }

    wpc_pures.
    wpc_bind (struct.loadF _ _ _).
    wpc_frame.
    wp_loadField.
    iNamed 1.
    wpc_pures.
    wpc_apply (wpc_Write' with "[$Hb Hbackup]").
    { iFrame. }
    iSplit; [ | iNext ].
    { iIntros "[Hbackup|Hbackup]"; try iFromCache.
      iSplitL "HΦ HQ HQc"; first by iFromCache.
      iExists _; iFrame.
      iExists _; iFrame. }
    iIntros "(Hbackup&Hb)".
    iSplitR "Hprimary Hbackup HP"; last first.
    { iExists _; iFrame. }
    iIntros "His_locked".
    iSplit; last by iFromCache.
    wpc_pures.
    wpc_frame.
    wp_loadField.
    wp_apply (crash_lock.release_spec with "[$His_locked]"); auto.
    iNamed 1.
    iApply "HΦ"; auto.
  Qed.

End goose.
