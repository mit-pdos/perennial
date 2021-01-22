From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.goose_nfsd Require Import twophase.
From Perennial.program_proof Require Import buftxn_proof.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof.
From Perennial.program_proof Require Import wal.abstraction.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.Helpers Require Import PropRestore.

Section goose_lang.
Context `{!buftxnG Σ}.
Context `{!heapG Σ}.

(* lock addrs are all block nums only *)

Definition get_mt_addrs (mt: gmap addr versioned_object) :=
  (λ x, addrBlock (fst x)) <$> (map_to_list mt).

Definition get_disk_addrs (d: disk) :=
  ((λ x, U64 (x.1 / (block_bytes * 8))) <$> (map_to_list d)).

Definition addr_wf (dinit: disk) a :=
  is_Some (dinit !! (addr2flat_z a)) ∧ int.Z (addrOff a) < block_bytes * 8.

Definition addr_wf' (dinit: disk) a :=
  (addrBlock a) ∈ get_disk_addrs dinit ∧ int.Z (addrOff a) < block_bytes * 8.

Lemma addr_wf_wf' dinit a:
  addr_wf dinit a → addr_wf' dinit a.
Proof.
  intros [Hblk Hoff].
  split.
  2: assumption.
  rewrite /get_disk_addrs.
  destruct Hblk as [b Hb].
  eapply elem_of_list_fmap_1_alt.
  1: apply elem_of_map_to_list; apply Hb.
  rewrite /addr2flat_z /addrBlock /=.
  rewrite -Z.mul_assoc Z.div_add_l.
  2: auto.
  rewrite Zdiv_small.
  all: word.
Qed.

Definition is_twophase_inner (l : loc) mt (locked_addrs: list u64) γ (dinit: disk) : iProp Σ := (
  ∃ (buftxnl locksl: loc) acquired_s anydirty ghs (dinit_addrs: gset u64) (acquired: list u64),
    let dinit_addrs := get_disk_addrs dinit in
    let mt_addrs := get_mt_addrs mt in
    "Htwophase.buftxn" ∷ l ↦[TwoPhase.S :: "buftxn"] #buftxnl ∗
    "Htwophase.locks" ∷ l ↦[TwoPhase.S :: "locks"] #locksl ∗
    "Htwophase.acquired" ∷ l ↦[TwoPhase.S :: "acquired"] (slice_val acquired_s) ∗
    "Hbuftxn" ∷ is_buftxn buftxnl mt γ dinit anydirty ∗
    "#Hlocks" ∷ is_lockMap locksl ghs (list_to_set dinit_addrs) (const True%I) ∗
    "Hacquired_s" ∷ is_slice acquired_s uint64T 1 locked_addrs ∗
    "Hlocked_addrs" ∷ ([∗ list] a ∈ locked_addrs, Locked ghs a) ∗
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
  iDestruct (struct_fields_split with "Hl") as "(Htwophase.buftxn & Htwophase.locks & Htwophase.acquired & %)".
  iExists _, _, _, _, _, _, _.
  rewrite /get_mt_addrs /get_disk_addrs map_to_list_empty /=.
  iFrame "# ∗".
  iSplit; first by auto.
  iSplit; first by auto.
  iPureIntro.
  apply list_subseteq_nil.
  Unshelve.
  - apply ∅.
  - apply [].
Qed.

Theorem wp_twophase__Acquire (l: loc) mt locked_addrs γ dinit a:
  {{{
    "Htwophase" ∷ is_twophase_inner l mt locked_addrs γ dinit ∗
    "%Ha_wf" ∷ ⌜addr_wf dinit a⌝
  }}}
    TwoPhase__Acquire #l (addr2val a)
  {{{
    RET #();
    let blk := addrBlock a in
    let locked_addrs' := if (decide (blk ∈ locked_addrs)) then
        locked_addrs else locked_addrs ++ [blk] in
    is_twophase_inner l mt locked_addrs' γ dinit
  }}}.
Proof.
  wp_start.
  wp_call.
  wp_apply wp_ref_to; first by auto.
  iIntros (already_acquired_l) "Halready_acquired_l".
  iNamed "Htwophase".
  wp_loadField.
  iDestruct (is_slice_small_read with "Hacquired_s") as "[Hacquired_s Hacquired_s_wrap]".
  wp_apply (wp_forSlicePrefix (λ done todo,
    let already_acquired_val := bool_decide (addrBlock a ∈ done) in
    "Halready_acquired_l" ∷ already_acquired_l ↦[boolT] #already_acquired_val
  )%I (V:=u64) with "[] [$Hacquired_s Halready_acquired_l]").
  2: {
    rewrite bool_decide_eq_false_2; first by iFrame.
    apply not_elem_of_nil.
  }
  {
    iIntros (i x done todo Harr Φ0).
    iModIntro.
    iNamed 1.
    iIntros "HΦ".
    wp_if_destruct.
    {
      wp_apply (wp_StoreAt with "[$Halready_acquired_l]").
      1: auto.
      iIntros "Halready_acquired_l".
      iApply "HΦ".
      rewrite bool_decide_eq_true_2; first by iFrame.
      apply elem_of_app.
      right.
      apply (iffRL (elem_of_list_singleton _ _)).
      reflexivity.
    }
    iApply "HΦ".
    destruct (decide (addrBlock a ∈ done)).
    - rewrite bool_decide_eq_true_2.
      2: assumption.
      rewrite bool_decide_eq_true_2; first by iFrame.
      apply elem_of_app.
      left.
      assumption.
    - rewrite bool_decide_eq_false_2.
      2: assumption.
      rewrite bool_decide_eq_false_2; first by iFrame.
      apply not_elem_of_app.
      split; first by assumption.
      intro Hin.
      apply elem_of_list_singleton in Hin.
      apply Heqb.
      f_equal.
      f_equal.
      apply Hin.
  }
  iIntros "[Hacquired_s ?]".
  iNamed.
  iApply "Hacquired_s_wrap" in "Hacquired_s".
  wp_apply (wp_LoadAt with "[$Halready_acquired_l]").
  iIntros "Halready_acquired_l".
  wp_if_destruct.
  2: {
    iApply "HΦ".
    rewrite decide_True.
    2: assumption.
    iExists _, _, _, _, _, _, _.
    iFrame "∗ # %".
  }
  rewrite bool_decide_eq_false_2.
  2: assumption.
  wp_loadField.
  apply addr_wf_wf' in Ha_wf.
  wp_apply (wp_LockMap__Acquire with "[$Hlocks]").
  {
    iPureIntro.
    apply elem_of_list_to_set.
    destruct Ha_wf.
    intuition.
  }
  iIntros "[_ Hlocked]".
  wp_loadField.
  wp_apply (wp_SliceAppend (V:=u64) with "[$Hacquired_s]").
  iIntros (acquired_s') "Hacquired_s".
  wp_apply (wp_storeField with "Htwophase.acquired").
  1: rewrite /field_ty /=; val_ty.
  iIntros "Htwophase.acquired".
  iApply "HΦ".
  rewrite decide_False.
  2: assumption.
  iExists _, _, _, _, _, _, _.
  iFrame "∗ #".
  iSplit; first by auto.
  destruct Ha_wf.
  iSplit; iPureIntro; set_solver.
  Unshelve.
  all: auto.
Qed.

Theorem wp_twophase__Release (l: loc) locked_addrs a γ dinit:
  {{{
    is_twophase_inner l ∅ (locked_addrs ++ [a]) γ dinit
  }}}
    TwoPhase__Release #l
  {{{
    RET #();
    is_twophase_inner l ∅ locked_addrs γ dinit
  }}}.
Proof.
  wp_start.
  wp_call.
  iNamed "Hpre".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_loadField.
  iDestruct (is_slice_small_read with "Hacquired_s") as "[Hacquired_s Hacquired_s_wrap]".
  iDestruct (is_slice_small_sz with "Hacquired_s") as "%Hacquired_s_sz".
  assert ((locked_addrs ++ [a]) !! (length locked_addrs) = Some a) as Hlocked_addrs_acc.
  {
    rewrite lookup_app_r.
    2: lia.
    rewrite Nat.sub_diag //.
  }
  rewrite app_length /= in Hacquired_s_sz.
  assert (int.nat acquired_s.(Slice.sz) > 0) as Hacquired_s_sz_gt by lia.
  wp_apply (wp_SliceGet (V:=u64) with "[$Hacquired_s]").
  {
    iPureIntro.
    replace (int.nat (word.sub _ 1)) with ((int.nat acquired_s.(Slice.sz)) - 1)%nat by word.
    rewrite -Hacquired_s_sz Nat.add_sub.
    apply Hlocked_addrs_acc.
  }
  iIntros "Hacquired_s".
  wp_loadField.
  iDestruct (big_sepL_app with "Hlocked_addrs") as "[Hlocked_addrs Hlocked]".
  rewrite big_sepL_singleton.
  wp_apply (wp_LockMap__Release with "[$Hlocks $Hlocked //]").
  wp_loadField.
  wp_apply (wp_SliceTake uint64T).
  1: word.
  wp_apply (wp_storeField with "Htwophase.acquired").
  1: rewrite /field_ty /=; val_ty.
  iIntros "Htwophase.acquired".
  iApply "HΦ".
  iExists _, _, _, _, _, _, _.
  iApply "Hacquired_s_wrap" in "Hacquired_s".
  iFrame "∗ #".
  iSplitL "Hacquired_s".
  {
    iApply (is_slice_take_cap _ _ _ (word.sub acquired_s.(Slice.sz) 1)) in "Hacquired_s".
    1: rewrite fmap_length app_length /=; word.
    replace (int.nat (word.sub _ 1)) with ((int.nat acquired_s.(Slice.sz)) - 1)%nat by word.
    rewrite -fmap_take -Hacquired_s_sz Nat.add_sub take_app.
    iFrame.
  }
  rewrite /get_mt_addrs map_to_list_empty /=.
  iSplit; iPureIntro; set_solver.
  Unshelve.
  all: auto.
Qed.

Theorem wp_twophase__ReleaseAll (l: loc) locked_addrs γ dinit:
  {{{
    is_twophase_inner l ∅ locked_addrs γ dinit
  }}}
    TwoPhase__ReleaseAll #l
  {{{
    RET #();
    is_twophase_inner l ∅ [] γ dinit
  }}}.
Proof.
  wp_start.
  wp_call.
  Check wp_forBreak_cond.
  wp_apply (wp_forBreak_cond (λ b,
    ∃ locked_addrs',
      "Htwophase" ∷ is_twophase_inner l ∅ locked_addrs' γ dinit ∗
      "%Hb" ∷ ⌜b = false → locked_addrs' = []⌝
  )%I with "[] [Hpre]").
  2: {
    iExists (locked_addrs).
    iFrame.
    auto.
  }
  {
    iModIntro.
    iIntros (Φ') "Hloop HΦ'".
    clear locked_addrs.
    iDestruct "Hloop" as (locked_addrs) "[? ?]".
    iNamed.
    iNamed "Htwophase".
    wp_loadField.
    wp_apply wp_slice_len.
    iDestruct (is_slice_sz with "Hacquired_s") as "%Hlocked_addrs_len".
    wp_if_destruct.
    2: {
      iApply "HΦ'".
      iExists locked_addrs.
      rewrite Heqb in Hlocked_addrs_len.
      replace (int.nat 0) with 0%nat in Hlocked_addrs_len by word.
      apply nil_length_inv in Hlocked_addrs_len.
      subst locked_addrs.
      iSplitL.
      2: auto.
      iExists _, _, _, _, _, _, _.
      iFrame "∗ #".
      rewrite /get_mt_addrs map_to_list_empty //=.
    }
    iAssert (is_twophase_inner l ∅ locked_addrs γ dinit) with
      "[Htwophase.buftxn Htwophase.locks Htwophase.acquired
      Hbuftxn Hacquired_s Hlocked_addrs]"
    as "Htwophase".
    {
      iExists _, _, _, _, _, _, _.
      iFrame "∗ # %".
    }
    apply u64_val_ne in Heqb.
    replace (int.Z 0) with 0 in Heqb by word.
    assert (int.nat acquired_s.(Slice.sz) ≠ 0%nat) as Hacquired_s_sz by word.
    rewrite -Hlocked_addrs_len in Hacquired_s_sz.
    assert (0 < length locked_addrs)%nat as Hlocked_addrs by lia.
    apply length_nonzero_neq_nil in Hlocked_addrs.
    apply exists_last in Hlocked_addrs.
    destruct Hlocked_addrs as (locked_addrs'&locked_tail&->).
    wp_apply (wp_twophase__Release with "Htwophase").
    iIntros "Htwophase".
    wp_pures.
    iApply "HΦ'".
    iExists _.
    iFrame.
    auto.
    Unshelve.
    all: auto.
  }
  iIntros "Hloop".
  clear locked_addrs.
  iDestruct "Hloop" as (locked_addrs) "[? ?]".
  iNamed.
  pose proof (Hb eq_refl) as Hlocked_addrs.
  subst.
  iApply "HΦ".
  iFrame.
Qed.
