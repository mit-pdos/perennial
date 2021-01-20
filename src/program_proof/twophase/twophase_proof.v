From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.goose_nfsd Require Import twophase.
From Perennial.program_proof Require Import buftxn_proof.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section goose_lang.
Context `{!buftxnG Σ}.
Context `{!heapG Σ}.

Definition get_mt_addrs (mt: gmap addr versioned_object) :=
  (λ x, addr2flat (fst x)) <$> (map_to_list mt).

Definition get_disk_addrs (d: disk) :=
  ((λ x, U64 (fst x)) <$> (map_to_list d)).

Definition is_twophase_inner (l : loc) mt (locked_addrs: list u64) γ (dinit: disk) : iProp Σ := (
  ∃ (buftxnl locksl: loc) acquired_s anydirty ghs (dinit_addrs: gset u64) (acquired: list u64),
    let dinit_addrs := get_disk_addrs dinit in
    let mt_addrs := get_mt_addrs mt in
    "Htwophase.buftxn" ∷ l ↦[TwoPhase.S :: "buftxn"] #buftxnl ∗
    "Htwophase.locks" ∷ l ↦[TwoPhase.S :: "locks"] #locksl ∗
    "Htwophase.acquired" ∷ l ↦[TwoPhase.S :: "acquired"] (slice_val acquired_s) ∗
    "Hbuftxn" ∷ is_buftxn buftxnl mt γ dinit anydirty ∗
    "#Hlocks" ∷ is_lockMap locksl ghs (list_to_set dinit_addrs) (const True%I) ∗
    "Hacquired_s" ∷ is_slice acquired_s uint64T 1 mt_addrs ∗
    "Hlocked_addrs" ∷ [∗ list] a ∈ locked_addrs, Locked ghs a ∗
    "%Hmt_addrs_locked" ∷ ⌜mt_addrs ⊆ locked_addrs⌝ ∗
    "%Hlocked_addrs_wf" ∷ ⌜locked_addrs ⊆ dinit_addrs⌝
)%I.

Definition is_twophase (l : loc) mt γ (dinit: disk) : iProp Σ := (
  is_twophase_inner l mt (get_mt_addrs mt) γ dinit
)%I.

Ltac wp_start :=
  iIntros (Φ) "Hpre HΦ";
  lazymatch goal with
  | |- context[Esnoc _ (INamed "HΦ") (▷ ?Q)%I] =>
    set (post:=Q)
  end;
  lazymatch iTypeOf "Hpre" with
  | Some (_, named _ _ ∗ _)%I => iNamed "Hpre"
  | Some (_, named _ _)%I => iNamed "Hpre"
  | _ => idtac
  end.

Theorem wp_twophase_Begin (txnl locksl: loc) γ dinit ghs:
  {{{
    "Htxn" ∷ invariant.is_txn txnl γ dinit ∗
    "#Hlocks" ∷ is_lockMap locksl ghs (list_to_set (get_disk_addrs dinit)) (const True%I)
  }}}
    Begin #txnl #locksl
  {{{
    (l : loc), RET #l;
    is_twophase l ∅ γ dinit
  }}}.
Proof.
  wp_start.
  wp_call.
  wp_apply (wp_buftxn_Begin with "Htxn").
  iIntros (buftxnl) "Hbuftxn".
  wp_apply (wp_NewSlice _ _ uint64T).
  iIntros (acquired_s) "Hacquired_s".
  wp_apply wp_allocStruct; first by auto.
  iIntros (l) "Hl".
  wp_pures.
  wp_apply util_proof.wp_DPrintf.
  wp_pures.
  iApply "HΦ".
  iExists _, _, _, _, _, _, _.
  iDestruct (struct_fields_split with "Hl") as "(Htwophase.buftxn & Htwophase.locks & Htwophase.acquired & %)".
  rewrite /get_mt_addrs /get_disk_addrs map_to_list_empty /=.
  iFrame "# ∗".
  Unshelve.
  - apply ∅.
  - apply [].
Qed.

Theorem wp_twophase__Acquire (l: loc) mt locked_addrs γ dinit a:
  {{{
    is_twophase_inner l mt locked_addrs γ dinit
  }}}
    TwoPhase__Acquire #l (addr2val a)
  {{{
    (l : loc), RET #l;
    let flata := addr2flat a in
    if (decide (flata ∈ locked_addrs)) then
      is_twophase_inner l mt locked_addrs γ dinit
    else
      is_twophase_inner l mt (locked_addrs ++ [addr2flat a]) γ dinit
  }}}.
Proof.
  wp_start.
  wp_call.
  wp_apply wp_ref_to; first by eauto.
  iIntros (already_acquired_l) "Halready_acquired_l".
  wp_pures.
  iNamed "Hpre".
  wp_loadField.
  iDestruct (is_slice_small_read with "Hacquired_s") as "[Hacquired_s Hacquired_s_wrap]".
  destruct (decide (addr2flat a ∈ locked_addrs)).
  {
    wp_apply (wp_forSlice (λ _,
      "Halready_acquired_l" ∷ already_acquired_l ↦[boolT] #false
    )%I with "[] [Hacquired_s $Halready_acquired_l]").
    2: admit.
    {
      iIntros (i x Φ0).
      iModIntro.
      iNamed 1.
      iIntros "HΦ".
      wp_pures.
      iApply "HΦ".
      iFrame.
    }
    iIntros "[Halready_acquired_l Hacquired_s]".
    wp_pures.
    admit.
  }
  admit.
Admitted.

Theorem wp_twophase__ReleaseAll (l: loc) mt locked_addrs γ dinit:
  {{{
    is_twophase_inner l mt locked_addrs γ dinit
  }}}
    TwoPhase__ReleaseAll #l
  {{{
    RET #();
    is_twophase_inner l mt [] γ dinit
  }}}.
Proof.
Admitted.
