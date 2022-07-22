From Perennial.program_proof.mvcc Require Import tuple_common.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Lemma val_to_ver_with_val_ty (x : val) :
  val_ty x (uint64T * (boolT * (uint64T * unitT))%ht) ->
  (∃ (b : u64)  (e : bool) (v : u64), x = ver_to_val (b, e, v)).
Proof.
  intros H.
  inversion_clear H. 
  { inversion H0. }
  inversion_clear H0.
  inversion_clear H.
  inversion_clear H1.
  { inversion H. }
  inversion_clear H.
  inversion_clear H1.
  inversion_clear H0.
  { inversion H. }
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H.
  exists x0, x1, x2.
  reflexivity.
Qed.

Lemma inv_ver_to_val (x y : pver) :
  ver_to_val x = ver_to_val y ->
  x = y.
Proof.
  intros H.
  inversion H.
  rewrite (surjective_pairing x).
  rewrite (surjective_pairing x.1).
  rewrite (surjective_pairing y).
  rewrite (surjective_pairing y.1).
  by rewrite H1 H2 H3.
Qed.

Lemma drop_1_tail {A : Type} (l : list A) :
  tail l = drop 1 l.
Proof.
  destruct l.
  - done.
  - simpl. rewrite drop_0. done.
Qed.

Lemma drop_tail_commute {A : Type} (n : nat) (l : list A) :
  tail (drop n l) = drop n (tail l).
Proof.
  do 2 rewrite drop_1_tail.
  do 2 rewrite drop_drop.
  f_equal.
  lia.
Qed.

Definition own_tuple_phys_vers tuple vers : iProp Σ :=
  ∃ versS,
    "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val versS) ∗
    "HversS" ∷ slice.is_slice versS (structTy Version) 1 (ver_to_val <$> vers).

(*****************************************************************)
(* func (tuple *Tuple) removeVersions(tid uint64)                *)
(*****************************************************************)
Theorem wp_tuple__removeVersions tuple (tid : u64) vers :
  {{{ own_tuple_phys_vers tuple vers ∧ ⌜vers ≠ []⌝ }}}
    Tuple__removeVersions #tuple #tid
  {{{ RET #();
        (∃ vers',
           own_tuple_phys_vers tuple vers' ∧
           (∃ vers_prefix, ⌜vers_prefix ≠ [] ∧ vers = vers_prefix ++ vers'⌝) ∧
           (⌜Forall (λ ver, int.Z tid ≤ int.Z ver.1.1) (tail vers')⌝) ∧
           (∃ ver, ⌜ver ∈ vers' ∧ int.Z ver.1.1 < int.Z tid⌝)) ∨
        (own_tuple_phys_vers tuple vers)
  }}}.
Proof.
  iIntros (Φ) "[HtuplePhys %Hnotnil] HΦ".
  iNamed "HtuplePhys".
  wp_call.

  iDestruct (is_slice_sz with "HversS") as "%HversLen".
  rewrite fmap_length in HversLen.
  iDestruct (is_slice_small_acc with "HversS") as "[HversX HversS]".

  (***********************************************************)
  (* var idx uint64                                          *)
  (* idx = uint64(len(tuple.vers)) - 1                       *)
  (* for {                                                   *)
  (*     if idx == 0 {                                       *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     ver := tuple.vers[idx]                              *)
  (*     if ver.begin < tid {                                *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     idx--                                               *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first auto.
  iIntros (idxR) "HidxR".
  wp_pures.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_store.
  wp_pures.
  set P := λ (b : bool), (∃ (idx : u64),
             "%Hbound" ∷ (⌜int.Z 0 ≤ int.Z idx < Z.of_nat (length vers)⌝) ∗
             "HidxR" ∷ idxR ↦[uint64T] #idx ∗
             "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val versS) ∗
             "HversX" ∷ is_slice_small versS (struct.t Version) 1 (ver_to_val <$> vers) ∗
             "%HallLe" ∷ (⌜Forall (λ ver, int.Z tid ≤ int.Z ver.1.1) (drop (S (int.nat idx)) vers)⌝) ∗
             "%Hexit" ∷ if b
                        then ⌜True⌝
                        else ⌜(int.Z idx = 0) ∨
                              (0 < int.Z idx ∧
                               ∃ ver, ver ∈ (drop (int.nat idx) vers) ∧
                               int.Z ver.1.1 < int.Z tid)⌝)%I.
  wp_apply (wp_forBreak P with "[] [-HΦ HversS]").
  { (* Loop body. *)
    clear Φ.
    iIntros (Φ).
    iModIntro.
    iIntros "Hloop HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.
    wp_if_destruct.
    { (* [idx = 0]. *)
      iApply "HΦ".
      iModIntro.
      unfold P.
      iExists _.
      eauto 10 with iFrame.
    }
    wp_load.
    wp_loadField.
    destruct (list_lookup_lt _ (ver_to_val <$> vers) (int.nat idx)) as [ver HSome].
    { rewrite fmap_length. word. }
    wp_apply (wp_SliceGet with "[HversX]"); first auto.
    iIntros "[HversX %Hval_ty]".
    destruct (val_to_ver_with_val_ty ver) as (b & d & v & ->); first auto.
    wp_pures.
    apply u64_val_ne in Heqb.
    rewrite list_lookup_fmap in HSome.
    apply fmap_Some_1 in HSome as (verx & Hlookup & Everx).
    wp_if_destruct.
    { iApply "HΦ".
      iModIntro.
      unfold P.
      iExists _.
      iFrame "% ∗".
      iPureIntro.
      right.
      split; first word.
      exists (b, d, v).
      split; last done.
      apply (elem_of_list_lookup_2 _ 0).
      rewrite lookup_drop.
      rewrite -plus_n_O.
      rewrite Hlookup.
      f_equal.
      symmetry.
      by apply inv_ver_to_val.
    }
    wp_load.
    wp_store.
    iApply "HΦ".
    iExists _.
    iFrame.
    iPureIntro.
    split; first word.
    split; last done.
    replace (S _) with (int.nat idx); last word.
    rewrite (drop_S _ (b, d, v)); last first.
    { rewrite Hlookup. f_equal. by apply inv_ver_to_val. }
    apply Forall_cons_2; last done.
    apply Znot_lt_ge in Heqb0.
    simpl.
    word.
  }
  { (* Loop entry. *)
    unfold P.
    iExists _.
    iFrame.
    iPureIntro.
    assert (Hgt : 0 < int.Z versS.(Slice.sz)).
    { destruct (nil_or_length_pos vers); first contradiction. word. }
    split; first word.
    split; last done.
    replace (S _) with (length vers); last word.
    by rewrite drop_all.
  }

  iIntros "Hloop".
  iNamed "Hloop".

  wp_pures.
  wp_load.
  wp_loadField.
  wp_apply wp_SliceSkip.
  { word. }
  wp_storeField.

  iDestruct ("HversS" with "HversX") as "HversS".
  iDestruct "HversS" as "[HversX HversC]".
  iDestruct (slice.is_slice_small_take_drop _ _ _ idx with "HversX") as "[HversX _]"; first word.
  iDestruct (slice.is_slice_cap_skip _ _ idx with "HversC") as "HversC"; first word.
  iDestruct (slice.is_slice_split with "[$HversX $HversC]") as "HversS".
  rewrite <- fmap_drop.

  iApply "HΦ".
  iModIntro.
  destruct Hexit as [? | [Hgt HexistsLt]].
  - iRight.
    rewrite H.
    change (Z.to_nat 0) with 0%nat.
    rewrite drop_0.
    iExists _.
    iFrame.
  - iLeft.
    set vers' := drop (int.nat idx) vers.
    iExists vers'.
    iSplit.
    { iExists _.
      iFrame.
    }
    iPureIntro.
    split.
    { exists (take (int.nat idx) vers).
      split.
      { apply length_nonzero_neq_nil.
        rewrite take_length_le; first word.
        word.
      }
      { symmetry. apply take_drop. }
    }
    split.
    { subst vers'.
      replace (tail _) with (drop (S (int.nat idx)) vers); first done.
      destruct vers; by rewrite drop_tail_commute.
    }
    { auto. }
Qed.

Local Lemma spec_find_ver_suffix vers vers_prefix vers_suffix ver (tid : u64) :
  vers = vers_prefix ++ vers_suffix ->
  spec_find_ver vers_suffix tid = Some ver ->
  spec_find_ver vers tid = Some ver.
Proof.
  intros Hvers Hlookup.
  unfold spec_find_ver, spec_find_ver_reverse in *.
  rewrite Hvers.
  rewrite reverse_app.
  rewrite foldl_app.
  rewrite Hlookup.
  by rewrite spec_find_ver_step_Some_noop.
Qed.

Local Lemma spec_lookup_suffix vers vers_prefix vers_suffix (tid : u64) :
  vers = vers_prefix ++ vers_suffix ->
  Exists (λ ver, int.Z ver.1.1 < int.Z tid) vers_suffix ->
  spec_lookup vers tid = spec_lookup vers_suffix tid.
Proof.
  intros Hsuffix HexistsLt.
  rewrite Exists_exists in HexistsLt.
  destruct HexistsLt as (ver & Hin & Hlt).
  destruct (spec_find_ver_lt_Some vers_suffix tid ver) as [ver' HSome]; [auto | auto |].
  
  unfold spec_lookup.
  rewrite HSome.
  rewrite (spec_find_ver_suffix vers vers_prefix vers_suffix ver'); done.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) RemoveVersions(tid uint64)                *)
(*                                                               *)
(* Notes:                                                        *)
(* 1. This method keeps all versions ending after [tid].         *)
(* 2. The precondition says that [tid] is less than or equal to  *)
(*    a lower bound of the minimal active tid.                   *)
(* 3. Call [txnMgr.getMinActiveTID] before calling this method.  *)
(*****************************************************************)
Theorem wp_tuple__RemoveVersions tuple (tid : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ min_tid_lb γ (int.nat tid) }}}
    Tuple__RemoveVersions #tuple #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> #Hgclb' HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked Htuple]".
  iNamed "Htuple".
  iNamed "Hphys".
  iNamed "Habst".
  iNamed "Hwellformed".
  wp_pures.

  (***********************************************************)
  (* tuple.removeVersions(tid)                               *)
  (***********************************************************)
  wp_apply (wp_tuple__removeVersions with "[Hvers HversS]").
  { unfold own_tuple_phys_vers. eauto with iFrame. }
  iIntros "HtuplePhys".
  
  iDestruct "HtuplePhys" as "[HtuplePhys | HtuplePhys]"; last first.
  { (* The list of physcial versions are not changed. *)
    iNamed "HtuplePhys".
    wp_pures.
    wp_loadField.
    iClear "Hgclb'".
    wp_apply (release_spec with "[-HΦ]"); first eauto 20 with iFrame.
    wp_pures.
    by iApply "HΦ".
  }

  (* The new list of physical versions is a suffix of the old one. *)
  iDestruct "HtuplePhys" as (vers') "(HtuplePhys & %Hsuffix & %HtailLe & %HtidGt)".
  clear versS.
  iNamed "HtuplePhys".
  wp_pures.

  assert (H2 : int.Z tidgc < int.Z tid).
  { destruct Hsuffix as [versPrefix [Hnotnil' Hsuffix]].
    destruct HtidGt as [verPivot [Hin HtidGt]].
    apply Z.le_lt_trans with (int.Z verPivot.1.1); last done.
    rewrite Forall_forall in HtidgcLe.
    apply HtidgcLe.
    rewrite Hsuffix.
    destruct versPrefix; first congruence.
    simpl.
    apply elem_of_app.
    by right.
  }
  
  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  destruct HtidGt as (verHead & Hin & HtidGt).
  destruct Hsuffix as (versPrefix & Hprefix & Hsuffix).
  wp_apply (release_spec with "[-HΦ]").
  { iFrame "Hlock Hlocked".
    iNext.
    do 2 iExists _.
    iExists tid, vers', vchain.
    iSplitL "Htidown Htidlast Hvers HversS".
    { eauto with iFrame. }
    iFrame "% # ∗".
    iSplit.
    { (* Prove [HtupleAbs]. *)
      iPureIntro.
      simpl.
      intros tidx Htidx.
      rewrite HtupleAbs; last word.
      f_equal.
      apply spec_lookup_suffix with versPrefix.
      { by rewrite Hsuffix. }
      { rewrite Exists_exists.
        exists verHead.
        split; [done | word].
      }
    }
    iPureIntro.
    split.
    { (* Prove [HtidlastGe]. *)
      rewrite Hsuffix in HtidlastGe.
      by apply Forall_app in HtidlastGe as [_ ?].
    }
    split.
    { (* Prove [HexistsLt]. *)
      intros tidx HtidxGZ Htidx.
      rewrite Exists_exists.
      exists verHead.
      split; [done | word].
    }
    { by apply elem_of_not_nil with verHead. }
  }
  wp_pures.
  by iApply "HΦ".
Qed.

End proof.
