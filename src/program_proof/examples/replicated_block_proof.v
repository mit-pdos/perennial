From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import ModArith.
From Perennial.goose_lang Require Import crash_modality wpr_lifting.
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
  Local Hint Extern 1 (environments.envs_entails _ (rblock_cinv _ _)) => unfold rblock_cinv : core.

  Theorem rblock_linv_to_cinv addr σ :
    rblock_linv addr σ -∗ rblock_cinv addr σ.
  Proof.
    iNamed 1.
    iFrame "Hprimary".
    iExists _; iFrame.
  Qed.

  (** the abstraction relation for the replicated block is written in HOCAP
  style, by quantifying over an arbitrary caller-specified predicate [P] of the
  block's state. *)
  Let N := nroot.@"replicated_block".
  Context (P: rblock.t → iProp Σ).

  (* low-level rblock state *)
  Definition rblock_state l d_ref m_ref addr : iProp Σ :=
      (* reflect coq values in program data structure *)
      "#d" ∷ readonly (l ↦[RepBlock.S :: "d"] #d_ref) ∗
      "#addr" ∷ readonly (l ↦[RepBlock.S :: "addr"] #addr) ∗
      "#m" ∷ readonly (l ↦[RepBlock.S :: "m"] #m_ref).

  Definition is_pre_rblock (l: loc) addr σ : iProp Σ :=
    "*" ∷ (∃ (d_ref m_ref: loc),
      "Hro_state" ∷ rblock_state l d_ref m_ref addr ∗
      "Hfree_lock" ∷ is_free_lock m_ref) ∗
    "Hlinv" ∷ rblock_linv addr σ.

  Definition is_rblock (k': nat) (l: loc) addr : iProp Σ :=
    ∃ (d_ref m_ref: loc),
      "Hro_state" ∷ rblock_state l d_ref m_ref addr ∗
      (* lock protocol *)
      "#Hlock" ∷ is_crash_lock N N (LVL k') #m_ref
        (∃ σ, "Hlkinv" ∷ rblock_linv addr σ ∗ "HP" ∷ P σ)
        (∃ σ, "Hclkinv" ∷ rblock_cinv addr σ ∗ "HP" ∷ P σ)
  .

  Global Instance is_rblock_Persistent k' l addr :
    Persistent (is_rblock k' l addr).
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

  Theorem replicated_block_cfupd {l} k' addr σ0 :
    is_pre_rblock l addr σ0 -∗
    ▷ P σ0 ={⊤}=∗
      is_rblock k' l addr ∗
      |C={⊤,∅}_(LVL (S k'))=> ∃ σ, rblock_cinv addr σ ∗ P σ.
  Proof.
    iIntros "Hpre HP"; iNamed "Hpre".

    (* actually initialize the lock *)
    iMod (alloc_crash_lock_cfupd N N k'
                             (∃ σ, "Hlkinv" ∷ rblock_linv addr σ ∗ "HP" ∷ P σ)%I
                             (∃ σ, "Hclkinv" ∷ rblock_cinv addr σ ∗ "HP" ∷ P σ)%I
            with "Hfree_lock [] [Hlinv HP]") as "(Hlk&$)".
    { iIntros "!>"; iNamed 1.
      iExists _; iFrame.
      iApply rblock_linv_to_cinv; iFrame. }
    { eauto with iFrame. }

    iModIntro.
    iExists _, _; iFrame.
  Qed.

  (* Open is the replicated block's recovery procedure, which constructs the
  in-memory state as well as recovering the synchronization between primary and
  backup, going from the crash invariant to the lock invariant. *)
  Theorem wpc_Open {k E2} (d_ref: loc) addr σ :
    {{{ rblock_cinv addr σ }}}
      Open #d_ref #addr @ NotStuck;LVL (S (S k)); ⊤;E2
    {{{ (l:loc), RET #l; is_pre_rblock l addr σ }}}
    {{{ rblock_cinv addr σ }}}.
  Proof.
    iIntros (Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    iDeexHyp "Hbackup".
    wpc_call.
    { eauto with iFrame. }
    iCache with "Hprimary Hbackup HΦ".
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
    iCache with "HΦ Hprimary Hbackup".
    { crash_case. eauto with iFrame. }

    (* allocate lock *)
    wpc_pures.
    wpc_bind (lock.new _).
    wpc_frame.
    wp_apply wp_new_free_lock.
    iIntros (m_ref) "Hfree_lock".
    iNamed 1.

    (* allocate struct *)
    rewrite -wpc_fupd.
    wpc_frame.
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
    rewrite /is_pre_rblock; eauto with iFrame.
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

  Lemma wpc_RepBlock__Read {k E2} {k' l} addr (primary: bool) :
    (S k < k')%nat →
    ∀ Φ Φc,
        "Hrb" ∷ is_rblock k' l addr ∗
        "Hfupd" ∷ (Φc (* crash condition before lin.point *) ∧
                   ▷ (∀ σ, ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P σ ∗ (Φc (* crash condition after lin.point *) ∧
                                                 (∀ s, is_block s 1 σ -∗ Φ (slice_val s))))) -∗
      WPC RepBlock__Read #l #primary @ NotStuck; LVL (S k); ⊤; E2 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (? Φ Φc) "Hpre"; iNamed "Hpre".
    iNamed "Hrb".
    iNamed "Hro_state".
    wpc_call.
    { by iLeft in "Hfupd". }
    iCache with "Hfupd". (* after we stripped the later, cache proof *)
    { by iLeft in "Hfupd". }
    wpc_frame_seq.
    wp_loadField.
    wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
    iIntros "His_locked"; iNamed 1.
    wpc_pures.
    wpc_bind (RepBlock__readAddr _ _); wpc_frame.
    wp_apply (wp_RepBlock__readAddr with "addr").
    iIntros (addr' Haddr'_eq).
    iNamed 1.

    wpc_bind_seq.
    crash_lock_open "His_locked".
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
      { by iLeft in "HQ". }
      iExists _; iFrame.
      iApply rblock_linv_to_cinv; iFrame. }
    iIntros (s) "(Haddr'&Hb)".
    iDestruct (is_slice_to_small with "Hb") as "Hb".
    iSpecialize ("Hlkinv" with "Haddr'").
    iSplitR "HP Hlkinv"; last by eauto with iFrame.
    (* TODO: why is this the second goal?
       RALF: because use_crash_locked puts [R] to the right. *)
    iIntros "His_locked".
    iCache Φc with "HQ".
    { by iLeft in "HQ". }
    iSplit; first by iFromCache.
    wpc_pures.
    wpc_frame.

    wp_loadField.
    wp_apply (crash_lock.release_spec with "[$His_locked]"); auto.
    wp_pures.
    iNamed 1.
    iRight in "HQ".
    iApply "HQ"; iFrame.
  Qed.

  Theorem wpc_RepBlock__Read_triple (Q: Block → iProp Σ) (Qc: iProp Σ) {k E2} {k' l} addr (primary: bool) :
    (S k < k')%nat →
    {{{ "Hrb" ∷ is_rblock k' l addr ∗ (* replicated block protocol *)
        "HQc" ∷ (∀ σ, Q σ -∗ Qc) ∗ (* crash condition after "linearization point" *)
        "Hfupd" ∷ (Qc (* crash condition before "linearization point" *) ∧
                   (∀ σ, ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P σ ∗ Q σ)) }}}
      RepBlock__Read #l #primary @ NotStuck; LVL (S k); ⊤; E2
    {{{ s b, RET (slice_val s); is_block s 1 b ∗ Q b }}}
    {{{ Qc }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    iApply wpc_RepBlock__Read; first done.
    iFrame "Hrb".
    iSplit.
    { iLeft in "Hfupd". iLeft in "HΦ". iApply "HΦ". done. }
    iNext. iIntros (σ) "HP". iRight in "Hfupd". iMod ("Hfupd" with "HP") as "[HP HQ]".
    iModIntro. iFrame "HP". iSplit.
    { iLeft in "HΦ". iApply "HΦ". iApply "HQc". done. }
    iIntros (s) "Hblock". iRight in "HΦ". iApply "HΦ". iFrame.
  Qed.

  Lemma wpc_RepBlock__Write {k E2} l k' addr (s: Slice.t) q (b: Block) :
    (S k < k')%nat →
    ∀ Φ Φc,
        "Hrb" ∷ is_rblock k' l addr ∗
        "Hb" ∷ is_block s q b ∗
        "Hfupd" ∷ (Φc ∧ ▷ (∀ σ, ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P b ∗ (Φc ∧ (is_block s q b -∗ Φ #())))) -∗
    WPC  RepBlock__Write #l (slice_val s) @ NotStuck; LVL (S k); ⊤; E2 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (? Φ Φc) "Hpre"; iNamed "Hpre".
    iNamed "Hrb".
    iNamed "Hro_state".
    wpc_call.
    { iLeft in "Hfupd"; auto. }
    iCache with "Hfupd".
    { iLeft in "Hfupd"; auto. }
    wpc_frame_seq.
    wp_loadField.
    wp_apply (crash_lock.acquire_spec with "Hlock"); auto.
    iIntros "His_locked".
    iNamed 1.

    wpc_pures.
    wpc_bind_seq.
    crash_lock_open "His_locked".
    iNamed 1.
    iNamed "Hlkinv".

    iCache with "HP Hprimary Hbackup Hfupd".
    { iSplitL "Hfupd"; first by iFromCache.
      eauto 10 with iFrame. }

    (* call to (lower-case) write, doing the actual writes *)
    wpc_call.
    wpc_bind (struct.loadF _ _ _).
    wpc_frame.
    wp_loadField.
    iNamed 1.
    (* first write *)
    (* This is an interesting example illustrating crash safety - notice that we
    produce [Q] atomically during this Write. This is the only valid simulation
    point in this example, because if we crash the operation has logically
    occurred due to recovery.

    Also note that this is quite different from the Perennial example which
    requires helping due to the possibility of losing the first disk block
    between crash and recovery - the commit cannot happen until recovery
    succesfully synchronizes the disks. *)
    wpc_apply (wpc_Write_fupd (⊤ ∖ ↑N) with "Hb").
    iModIntro. iExists _; iFrame. iIntros "!> Hprimary".
    (* linearization/simulation point: run Hfupd. *)
    iRight in "Hfupd". iMod ("Hfupd" with "HP") as "[HP HΦ]".
    iModIntro. iSplit.
    { iLeft in "HΦ". eauto 10 with iFrame. }
    iIntros "Hb".
    iCache Φc with "HΦ".
    { by iLeft in "HΦ". }

    wpc_pures.
    { iSplitL "HΦ"; first iFromCache. eauto 10 with iFrame. }
    iCache with "HΦ Hprimary Hbackup HP".
    { iSplitL "HΦ"; first iFromCache. eauto 10 with iFrame. }
    wpc_bind (struct.loadF _ _ _).
    wpc_frame.
    wp_loadField.
    iNamed 1.
    wpc_pures.
    (* second write *)
    wpc_apply (wpc_Write' with "[$Hb Hbackup]").
    { iFrame. }
    iSplit; [ | iNext ].
    { iIntros "[Hbackup|Hbackup]"; try iFromCache.
      iSplitL "HΦ"; first by iFromCache. eauto 10 with iFrame. }
    iIntros "(Hbackup&Hb)".
    iSplitR "Hprimary Hbackup HP"; last first.
    { eauto with iFrame. }
    iIntros "His_locked".
    iSplit; first iFromCache.
    wpc_pures.
    wpc_frame.
    wp_loadField.
    wp_apply (crash_lock.release_spec with "[$His_locked]"); auto.
    iNamed 1.
    iApply "HΦ"; iFrame.
  Qed.

  Theorem wpc_RepBlock__Write_triple (Q: iProp Σ) (Qc: iProp Σ) {k E2} l k' addr (s: Slice.t) q (b: Block) :
    (S k < k')%nat →
    {{{ "Hrb" ∷ is_rblock k' l addr ∗
        "Hb" ∷ is_block s q b ∗
        "HQc" ∷ (Q -∗ Qc) ∗
        "Hfupd" ∷ (Qc ∧ (∀ σ, ▷ P σ ={⊤ ∖ ↑N}=∗ ▷ P b ∗ Q)) }}}
      RepBlock__Write #l (slice_val s) @ NotStuck; LVL (S k); ⊤; E2
    {{{ RET #(); Q ∗ is_block s q b }}}
    {{{ Qc }}}.
  Proof.
    iIntros (? Φ Φc) "Hpre HΦ"; iNamed "Hpre".
    iApply wpc_RepBlock__Write; first done.
    iFrame. iSplit.
    { iLeft in "Hfupd". iLeft in "HΦ". iApply "HΦ". done. }
    iNext. iIntros (σ) "HP". iRight in "Hfupd". iMod ("Hfupd" with "HP") as "[HP HQ]".
    iModIntro. iFrame "HP". iSplit.
    { iLeft in "HΦ". iApply "HΦ". iApply "HQc". done. }
    iIntros "Hblock". iRight in "HΦ". iApply "HΦ". iFrame.
  Qed.

  (* Silly example client *)
  Definition OpenRead (d_ref: loc) (addr: u64) : expr :=
    (let: "l" := Open #d_ref #addr in
     RepBlock__Read "l" #true).

  Theorem wpc_OpenRead (d_ref: loc) {E2} addr σ:
    {{{ rblock_cinv addr σ ∗ P σ }}}
      OpenRead d_ref addr @ NotStuck; LVL 100; ⊤; E2
    {{{ (x: val), RET x; True }}}
    {{{ ∃ σ, rblock_cinv addr σ ∗ P σ }}}.
  Proof using stagedG0.
    rewrite /OpenRead.
    iIntros (??) "(H&HP) HΦ".
    wpc_bind (Open _ _).
    wpc_apply (wpc_Open with "H").
    iSplit.
    { iIntros "H". iLeft in "HΦ". iApply "HΦ". eauto with iFrame. }
    iNext. iIntros (?) "Hpre".
    iMod (replicated_block_cfupd 98 with "Hpre HP") as "(#Hrblock&Hcfupd)".
    (* Here is the use of the cfupd to cancel out the rblock_cinv from crash condition,
       which is important because RepBlock__Read doesn't guarantee rblock_cinv! *)
    iMod "Hcfupd" as "_".
    iCache with "HΦ".
    { by iLeft in "HΦ". }
    wpc_pures.
    (* Weaken the levels. *)
    iApply (wpc_idx_mono _ (LVL 50)).
    { apply LVL_le. lia. }
    wpc_apply (wpc_RepBlock__Read with "[HΦ $Hrblock]").
    { lia. }
    iSplit; first iFromCache.
    iNext. iIntros. iModIntro. iFrame "# ∗".
    iSplit; first iFromCache.
    iIntros. iRight in "HΦ". iApply "HΦ".
    eauto.
  Qed.

End goose.

Typeclasses Opaque rblock_cinv.

(* rblock_cinv is durable *)
Instance rblock_crash `{!heapG Σ} addr σ :
  IntoCrash (rblock_cinv addr σ) (λ _, rblock_cinv addr σ).
Proof.
  rewrite /IntoCrash /rblock_cinv. iIntros "?".
  iCrash. iFrame.
Qed.

Section recov.
  Context `{!heapG Σ}.
  Context `{!crashG Σ}.
  Context `{!stagedG Σ}.

  (* This has to be in a separate section from the wpc lemmas because we will
     use different heapG instances after crash *)

  (* Just a simple example of using idempotence *)
  Theorem wpr_Open (d_ref: loc) k addr σ:
    rblock_cinv addr σ -∗
    wpr NotStuck (LVL (S (S k))) ⊤
        (Open #d_ref #addr)
        (Open #d_ref #addr)
        (λ _, True%I)
        (λ _, True%I)
        (λ _ _, True%I).
  Proof.
    iIntros "Hstart".
    iApply (idempotence_wpr _ (LVL (S (S k))) ⊤ ⊤ _ _ _ _ _ (λ _, ∃ σ, rblock_cinv addr σ)%I with "[Hstart]").
    { auto. }
    { wpc_apply (wpc_Open with "Hstart").
      iSplit; eauto.
    }
    iAlways. iIntros (?????) "H".
    iDestruct "H" as (σ') "Hstart".
    iNext. iCrash.
    iIntros.
    iSplit; first done.
    wpc_apply (wpc_Open with "Hstart").
    iSplit; eauto.
  Qed.

  Notation K := 100%nat.


  Theorem wpr_OpenRead (d_ref: loc) addr σ:
    rblock_cinv addr σ -∗
    wpr NotStuck (LVL 100) ⊤
        (OpenRead d_ref addr)
        (OpenRead d_ref addr)
        (λ _, True%I)
        (λ _, True%I)
        (λ _ _, True%I).
  Proof using stagedG0.
    iIntros "Hstart".
    iApply (idempotence_wpr _ (LVL 100) ⊤ ⊤ _ _ _ _ _ (λ _, ∃ σ, rblock_cinv addr σ ∗ True)%I with "[Hstart]").
    { auto. }
    { wpc_apply (wpc_OpenRead (λ _, True)%I with "[$Hstart]").
      iSplit; eauto.
    }
    iAlways. iIntros (?????) "H".
    iDestruct "H" as (σ') "(Hstart&_)".
    iNext. iCrash.
    (* XXX: iCrash should not have unfolded rblock_inv *)
    iIntros (??).
    iSplit; first done.
    wpc_apply (wpc_OpenRead (λ _, True)%I with "[$Hstart] []").
    iSplit; eauto.
  Qed.
End recov.

Existing Instances subG_stagedG.

From Perennial.program_logic Require Import recovery_adequacy.
From Perennial.goose_lang Require Export adequacy recovery_adequacy.
Definition repΣ := #[stagedΣ; heapΣ; crashΣ].

Theorem OpenRead_adequate σ dref addr :
  (* We assume the addresses we replicate are in the disk domain *)
  int.val addr ∈ dom (gset Z) (σ.(world) : (@ffi_state disk_model)) →
  int.val (word.add addr 1) ∈ dom (gset Z) (σ.(world) : (@ffi_state disk_model)) →
  recv_adequate (CS := heap_crash_lang) NotStuck (OpenRead dref addr) (OpenRead dref addr)
                σ (λ v _, True) (λ v _, True) (λ _, True).
Proof.
  rewrite ?elem_of_dom.
  intros (d1&Hin1) (d2&Hin2).
  apply (heap_recv_adequacy (repΣ) _ (LVL 100) _ _ _ _ _ _ (λ _, True)%I).
  { simpl. auto. }
  iIntros (??) "Hstart _ _".
  iModIntro.
  iSplitL "".
  { iAlways; iIntros. iMod (fupd_intro_mask' _ ∅); eauto. }
  iSplitL "".
  { iAlways; iIntros. iAlways. iMod (fupd_intro_mask' _ ∅); eauto. }
  iApply wpr_OpenRead.
  rewrite /ffi_start//=.
  rewrite /rblock_cinv.
  iDestruct (big_sepM_delete _ _ (int.val addr) with "Hstart") as "(Hd1&Hmap)"; first eapply Hin1.
  iDestruct (big_sepM_delete _ _ (int.val (word.add addr 1)) with "Hmap") as "(Hd2&Hmap)".
  { rewrite lookup_delete_ne //=.
    apply word_add1_neq. }
  iFrame. iExists _. iFrame.
Qed.
