From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Export marshal_proof memkv.common_proof.

(*
  Defines Coq request and reply types for shard server InstallShard RPC. Also defines
  has_encoding for InstallShard Request/Reply and provides WPs for {de|en}codeInstallShardRe{ply|quest}()
 *)

Section memkv_marshal_install_shard_proof.

Record InstallShardRequestC := mkInstallShardC {
  IR_Sid : u64;
  IR_Kvs : gmap u64 (list u8)
}.

(* A marshalled map requires:
   - 8 bytes to record the number of keys
   - 8 bytes per key to record the key (8 * size m)
   - 8 bytes per key to record the length of the slice for that key's value
   - 1 byte * length of each value to record the values *)
Definition marshalledMapSize_data (m : gmap u64 (list u8)) : nat :=
  map_fold (λ k v tot, 8 + 8 + length v + tot)%nat O m.

Definition marshalledMapSize (m: gmap u64 (list u8)) : nat :=
  8 + marshalledMapSize_data m.

Lemma marshalledMapSize_data_delete m k l :
  m !! k = Some l →
  marshalledMapSize_data m = (16 + length l + marshalledMapSize_data (delete k m))%nat.
Proof.
  intros Hlookup.
  rewrite /marshalledMapSize_data.
  assert (m = <[k := l]> (delete k m)) as Heq.
  { rewrite insert_delete_insert. rewrite insert_id //. }
  rewrite Heq.
  rewrite map_fold_insert_L //; last by apply lookup_delete.
  { rewrite insert_delete_insert.
    rewrite delete_insert_delete. lia. }
  intros.
  lia.
Qed.

Lemma marshalledMapSize_data_insert m k l :
  m !! k = None →
  marshalledMapSize_data (<[k := l]>m) = (16 + length l + marshalledMapSize_data m)%nat.
Proof.
  intros Hlookup.
  rewrite /marshalledMapSize_data.
  rewrite map_fold_insert_L //.
  intros.
  lia.
Qed.


(*
Definition marshalledMapSize (m:gmap u64 (list u8)) : nat :=
  8 + 2 * (size m)
*)

Definition has_byte_map_encoding (m:gmap u64 (list u8)) (r:Rec) :=
  ∃ l,
  (uint.Z (size m) = size m) ∧
  NoDup l.*1 ∧
  (list_to_map l) = m ∧
  r = [EncUInt64 (size m)] ++
      ((flat_map (λ u, [EncUInt64 u.1 ; EncUInt64 (uint.Z (length (u.2))); EncBytes u.2]) l)).

Definition has_encoding_InstallShardRequest (data:list u8) (args:InstallShardRequestC) : Prop :=
  ∃ r, (* (∀ k, k ∈ dom (gset _ ) args.(IR_Kvs) → shardOfC k = args.(IR_CID)) ∧ *)
       has_byte_map_encoding (args.(IR_Kvs)) r ∧
       has_encoding data ([EncUInt64 args.(IR_Sid)] ++ r).

Context `{!heapGS Σ}.

Definition own_slicemap_rep (mv : gmap u64 val) (m : gmap u64 (list u8)) : iProp Σ :=
  "%Hmdoms" ∷ ⌜ dom mv = dom m ⌝ ∗
  "Hmvals" ∷ ([∗ map] k ↦ v ∈ mv, (∃ vsl, ⌜ v = slice_val vsl ⌝ ∗
              typed_slice.own_slice_small vsl byteT DfracDiscarded (default [] (m !! k))))%I.

Lemma own_slicemap_rep_dom  mv m :
  own_slicemap_rep mv m -∗ ⌜ dom mv = dom m ⌝.
Proof. iIntros "($&_)". Qed.

Lemma own_slicemap_rep_empty_inv m :
  own_slicemap_rep ∅ m -∗ ⌜ m = ∅ ⌝.
Proof.
  iIntros "(%Hdom&_)".
  iPureIntro. rewrite dom_empty_L in Hdom.
  apply dom_empty_inv_L. eauto.
Qed.

Lemma own_slicemap_rep_dup mv m :
  own_slicemap_rep mv m -∗ own_slicemap_rep mv m ∗ own_slicemap_rep mv m.
Proof.
  iIntros "Hrep".
  rewrite /own_slicemap_rep.
  iNamed "Hrep". iFrame "%".
  rewrite -big_sepM_sep.
  iApply (big_sepM_mono with "Hmvals").
  iIntros (k x Hlookup) "H".
  iDestruct "H" as (vsl Heq) "#Hslice".
  iSplitL.
  { iExists _. iFrame. eauto. }
  { iExists _. iFrame. eauto. }
Qed.

Lemma own_slicemap_rep_move1 m1 m1' m2 m2' k l l':
  m2 !! k = None →
  m1 !! k = Some l →
  m1' !! k = Some l' →
  own_slicemap_rep m1 m1' -∗
  own_slicemap_rep m2 m2' -∗
  (own_slicemap_rep (delete k m1) (delete k m1') ∗
   own_slicemap_rep (<[k := l]> m2) (<[k := l']> m2')).
Proof.
  iIntros (Hnone Hl Hl') "Hs1 Hs2".
  iNamed "Hs1".
  iRename "Hmvals" into "Hmvals1".
  iNamed "Hs2".
  iRename "Hmvals" into "Hmvals2".
  iDestruct (big_sepM_delete with "Hmvals1") as "(Hl&Hmvals1)"; eauto.
  iSplitL "Hmvals1".
  { iSplit; first iPureIntro.
    { rewrite ?dom_delete_L Hmdoms. eauto. }
    iApply (big_sepM_mono with "Hmvals1").
    { iIntros (?? Hldel) "H". iDestruct "H" as (? Heq) "H". iExists _. iFrame "%".
      rewrite lookup_delete_ne //.
      intros Heq'. rewrite Heq' lookup_delete in Hldel. congruence. }
  }
  iSplit; first iPureIntro.
  { rewrite ?dom_insert_L; congruence. }
  iApply (big_sepM_insert_2 with "[Hl]"); auto.
  { simpl. iDestruct "Hl" as (? Heql) "H". iExists _. iFrame "%".
    rewrite lookup_insert. rewrite Hl'. eauto. }
  iApply (big_sepM_mono with "Hmvals2").
  { iIntros (k' ? Hldel) "H". iDestruct "H" as (? Heq) "H". iExists _. iFrame "%".
    destruct (decide (k = k')).
    { subst. congruence. }
    rewrite lookup_insert_ne //.
  }
Qed.

Lemma own_slicemap_lookup_l mv m k v :
  mv !! k = Some v →
  own_slicemap_rep mv m -∗
  own_slicemap_rep mv m ∗
  ∃ q vsl l, ⌜ v = slice_val vsl ⌝ ∗ ⌜ m !! k = Some l ⌝ ∗
   typed_slice.own_slice_small vsl byteT q l.
Proof.
  iIntros (Hlookup) "Hrep".
  iDestruct (own_slicemap_rep_dup with "Hrep") as "(Hrep&$)".
  iNamed "Hrep".
  iDestruct (big_sepM_lookup with "Hmvals") as (vsl Heq) "H"; eauto.
  assert (is_Some (m !! k)) as (l&Heq').
  { apply elem_of_dom_2 in Hlookup. rewrite Hmdoms in Hlookup. apply elem_of_dom in Hlookup. eauto. }
  iExists DfracDiscarded, vsl, l. iFrame "%". rewrite Heq' //.
Qed.

Definition EncSliceMap_invariant m0 enc_v (r:Rec) sz map_sz
           (original_remaining:Z) (mtodo' mdone':gmap u64 val) : iProp Σ :=
  ∃ mtodo mdone (l:list (u64 * (list u8))) (remaining:Z),
    own_slicemap_rep mtodo' mtodo ∗
    own_slicemap_rep mdone' mdone ∗
    ⌜ mtodo ∪ mdone = m0 ⌝ ∗
    ⌜ NoDup l.*1 ⌝ ∗
    ⌜(list_to_map l) = mdone⌝ ∗
    ⌜marshalledMapSize_data mtodo ≤ remaining⌝ ∗
    ⌜remaining = (original_remaining - marshalledMapSize_data mdone)%Z⌝ ∗
    ⌜mtodo ##ₘ mdone ⌝ ∗
    is_enc enc_v sz (r ++ [EncUInt64 map_sz] ++
 (flat_map (λ u, [EncUInt64 u.1 ; EncUInt64 (uint.Z (length (u.2))); EncBytes u.2]) l )) remaining
.


Definition own_InstallShardRequest args_ptr args : iProp Σ :=
  ∃ (kvs_ptr:loc) (mv:gmap u64 goose_lang.val),
  "HKey" ∷ args_ptr ↦[InstallShardRequest :: "Sid"] #args.(IR_Sid) ∗
  "HKvs" ∷ args_ptr ↦[InstallShardRequest :: "Kvs"] #kvs_ptr ∗
  "HKvsMap" ∷ map.own_map kvs_ptr (DfracOwn 1) (mv, (slice_val Slice.nil)) ∗
  "%Hdom_install" ∷ ⌜dom args.(IR_Kvs) = dom mv ⌝ ∗
  "Hvals" ∷ ([∗ set] k ∈ (fin_to_set u64),
        ⌜shardOfC k ≠ args.(IR_Sid) ∧ mv !! k = None ∧ args.(IR_Kvs) !! k = None⌝ ∨ (∃ vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.own_slice_small vsl byteT DfracDiscarded (default [] (args.(IR_Kvs) !! k))) )
.

Lemma wp_EncSliceMap e mref mv m sz r remaining :
  marshalledMapSize m <= remaining →
  {{{
      "HKvsMap" ∷ map.own_map mref (DfracOwn 1) (mv, slice_val Slice.nil) ∗
      "Henc" ∷ is_enc e sz r remaining ∗
      "Hvals" ∷ own_slicemap_rep mv m
  }}}
    EncSliceMap e #mref
  {{{
       rmap, RET #();
       ⌜has_byte_map_encoding m rmap⌝ ∗
       map.own_map mref (DfracOwn 1) (mv, slice_val Slice.nil) ∗
       own_slicemap_rep mv m ∗
       is_enc e sz (r ++ rmap) (remaining - marshalledMapSize m)
  }}}.
Proof using Type*.
  intros Hrem.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam. wp_pures.
    iDestruct (own_slicemap_rep_dom with "[$]") as %Hdom_init.

  wp_apply (map.wp_MapLen with "HKvsMap").
  iIntros "[%Hsize Hmap]".
  unfold marshalledMapSize in Hrem.
  wp_apply (wp_Enc__PutInt with "Henc").
  { lia. }
  iIntros "Henc".
  wp_pures.
  wp_apply (map.wp_MapIter_2 _ _ _ _ _ (EncSliceMap_invariant m e r sz (size m) (remaining - 8))
              with "Hmap [Henc Hvals] [] [HΦ]").
  {
    iExists m, ∅.
    iExists []. iExists (remaining-8). simpl. iFrame.
    iSplitL "".
    { rewrite /own_slicemap_rep. rewrite ?dom_empty_L big_sepM_empty //=. }
    iSplit.
    { iPureIntro. rewrite right_id_L //. }
    iSplit.
    { iPureIntro. apply NoDup_nil_2. }
    iSplit; first done.
    rewrite ?Map.map_size_dom Hdom_init //.
    rewrite ?Map.map_size_dom // in Hrem.
    iFrame.
    iPureIntro.
    split; first by lia.
    rewrite /marshalledMapSize_data. rewrite map_fold_empty.
    split; first by lia. apply map_disjoint_empty_r.
  }
  {
    clear Φ.
    iIntros (?? mtodo' mdone' Φ) "!# [Hpre %Htodo] HΦ".
    wp_pures.
    iDestruct "Hpre" as (mtodo mdone l rem') "Hpre".
    iDestruct "Hpre" as "(Hrep_todo&Hrep_done&Hpre)".
    iDestruct "Hpre" as (Hunion Hnodup Hl Hrem' Hremeq Hmdisjoint) "Henc".
    iDestruct (own_slicemap_rep_dom with "Hrep_todo") as %Hdom_todo.
    iDestruct (own_slicemap_rep_dom with "Hrep_done") as %Hdom_done.
    assert (16 <= marshalledMapSize_data mtodo).
    {
      assert (is_Some (mtodo !! k)) as (vl&Heq_vl).
      { apply elem_of_dom_2 in Htodo. rewrite Hdom_todo in Htodo. apply elem_of_dom. eauto. }
      erewrite marshalledMapSize_data_delete; last eauto.
      lia.
    }
    wp_apply (wp_Enc__PutInt with "Henc").
    {
      lia.
    }
    iIntros "Henc".
    wp_pures.

    iDestruct (own_slicemap_lookup_l with "Hrep_todo") as "(Hrep_todo&Hval)"; eauto.
    iDestruct "Hval" as (q vsl l' Heq1 Heq2) "Hslice".

    subst. wp_apply (wp_slice_len).
    wp_apply (wp_Enc__PutInt with "Henc").
    {
      lia.
    }
    iIntros "Henc".
    wp_pures.
    wp_apply (wp_Enc__PutBytes with "[$Henc $Hslice]").
    {
      erewrite (marshalledMapSize_data_delete mtodo) in Hrem' ; last eassumption.
      lia.
    }
    iIntros "(Henc&Hslice)".
    iApply "HΦ".
    iExists (delete k mtodo), (<[k := l']> (list_to_map l)).
    iExists (l ++ [(k, l')]), ((remaining - 8 - marshalledMapSize_data (list_to_map l) - 8 - 8 - length l')).
    assert (k ∉ dom (list_to_map l : gmap u64 (list u8))).
    { intros Hin. apply map_disjoint_dom_1 in Hmdisjoint.
      apply elem_of_dom_2 in Heq2. eauto. }
    iDestruct (own_slicemap_rep_move1 with "Hrep_todo Hrep_done") as "($&$)".
    { apply not_elem_of_dom. rewrite Hdom_done. set_solver. }
    { eauto. }
    { eauto. }
    assert (NoDup (l ++ [(k, l')]).*1).
    { rewrite fmap_app; simpl.
      apply NoDup_app; split_and!; eauto.
      { intros x Hinl. intros. intros Hin. apply elem_of_list_singleton in Hin; subst.
        apply map_disjoint_dom_1 in Hmdisjoint.
        rewrite dom_list_to_map_L in Hmdisjoint.
        assert (k ∈ (list_to_set l.*1 : gset u64)).
        { apply elem_of_list_to_set. eauto. }
        apply elem_of_dom_2 in Heq2. set_solver.
      }
      apply NoDup_singleton.
    }
    iSplit.
    { iPureIntro. rewrite union_delete_insert //. }
    iSplit; first done.
    iSplit.
    { iPureIntro. rewrite -list_to_map_cons. eapply list_to_map_proper; eauto.
      rewrite Permutation_app_comm //. }
    iSplit.
    {
      iPureIntro.
      erewrite marshalledMapSize_data_delete in Hrem'; eauto.
      lia.
    }
    iSplit.
    {
      iPureIntro.
      rewrite marshalledMapSize_data_insert; last first.
      { apply not_elem_of_dom. eauto. }
      lia.
    }
    iSplit.
    {
      iPureIntro.
      apply map_disjoint_dom_2.
      apply map_disjoint_dom_1 in Hmdisjoint.
      rewrite dom_delete_L dom_insert_L. set_solver.
    }
    iDestruct (typed_slice.own_slice_small_sz with "Hslice") as %Hsz'.
    iExactEq "Henc".
    f_equal.
    simpl.
    rewrite -?app_assoc; f_equal.
    simpl. f_equal.
    rewrite flat_map_app //=. repeat f_equal.
    word.
  }
  iIntros "(Hmap&Hinv)".
  iNamed "Hinv".
  wp_pures. iModIntro.
  iApply ("HΦ" $! ([EncUInt64 (size m)] ++
                 flat_map (λ u : u64 * list u8, [EncUInt64 u.1; EncUInt64 (uint.Z (length u.2)); EncBytes u.2]) l)).
  iDestruct "Hinv" as "(?&?&%Hunion&%&%&%&->&%&Henc)".
  iFrame.
  rewrite /marshalledMapSize.
  iDestruct (own_slicemap_rep_empty_inv with "[$]") as %Hemp.
  assert (m = mdone) as Hdone.
  { rewrite Hemp left_id_L in Hunion. auto. }
  rewrite Hdone.
  iSplit.
  { iPureIntro.
    rewrite /has_byte_map_encoding. eexists.
    split_and!; eauto.
    assert (size mdone = size mv) as ->; last first.
    { simpl in Hsize. word. }
    rewrite ?Map.map_size_dom. congruence.
  }
  iSplitR "Henc"; last first.
  { iExactEq "Henc". f_equal. lia. }
  iFrame.
Qed.

Definition SizeOfMarshalledMap_invariant m0 (s : loc) (mtodo' mdone':gmap u64 val) : iProp Σ :=
  (∃ (z : u64) mtodo mdone,
    own_slicemap_rep mtodo' mtodo ∗
    own_slicemap_rep mdone' mdone ∗
    ⌜ mtodo ∪ mdone = m0 ⌝ ∗
    ⌜mtodo ##ₘ mdone ⌝ ∗
    s ↦[uint64T] #z ∗
    ⌜ (8 + marshalledMapSize_data mdone)%nat = uint.nat z ⌝).

Lemma wp_SizeOfMarshalledMap mref mv m :
  {{{
      "HKvsMap" ∷ map.own_map mref (DfracOwn 1) (mv, slice_val Slice.nil) ∗
      "Hvals" ∷ own_slicemap_rep mv m
  }}}
    SizeOfMarshalledMap #mref
  {{{
       (z : u64), RET #z; ⌜ uint.nat z = marshalledMapSize m ⌝ ∗
       map.own_map mref (DfracOwn 1) (mv, slice_val Slice.nil) ∗
       own_slicemap_rep mv m
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_pures.
  rewrite /SizeOfMarshalledMap.
  wp_pure _.
  wp_apply (wp_ref_of_zero _ _ (uint64T)); first done.
  iIntros (s) "Hs".
  wp_pures.
  wp_apply (wp_StoreAt with "[$]"); first eauto.
  iIntros "Hs".
  wp_pures.
  wp_apply (map.wp_MapIter_2 _ _ _ _ _ (SizeOfMarshalledMap_invariant m s)
              with "HKvsMap [Hs Hvals] [] [HΦ]").
  {
    iExists (W64 8), m, ∅.
    simpl. iFrame.
    iSplitL "".
    { rewrite /own_slicemap_rep. rewrite ?dom_empty_L big_sepM_empty //=. }
    iSplit.
    { iPureIntro. rewrite right_id_L //. }
    iPureIntro; split.
    * apply map_disjoint_empty_r.
    * rewrite /marshalledMapSize_data map_fold_empty. word.
  }
  {
    clear Φ.
    iIntros (?? mtodo' mdone' Φ) "!# [Hpre %Htodo] HΦ".
    wp_pures.
    iDestruct "Hpre" as (z mtodo mdone) "Hpre".
    iDestruct "Hpre" as "(Hrep_todo&Hrep_done&%Hunion&%Hdisj&Hs&%Hsum)".
    iDestruct (own_slicemap_rep_dom with "Hrep_todo") as %Hdom_todo.
    iDestruct (own_slicemap_rep_dom with "Hrep_done") as %Hdom_done.
    iDestruct (own_slicemap_lookup_l with "Hrep_todo") as "(Hrep_todo&Hval)"; eauto.
    iDestruct "Hval" as (q vsl l' Heq1 Heq2) "Hslice".
    iDestruct (typed_slice.own_slice_small_sz with "Hslice") as %Hsz'.
    subst. wp_apply (wp_slice_len).
    wp_apply (wp_SumAssumeNoOverflow).
    iIntros (Hnooverflow1).
    wp_apply (wp_LoadAt with "[$]").
    iIntros "Hs".
    wp_apply (wp_SumAssumeNoOverflow).
    iIntros (Hnooverflow2).
    wp_pures.
    wp_apply (wp_StoreAt with "[$]").
    { eauto. }
    iIntros "Hs".
    iApply "HΦ".
    iExists _, (delete k mtodo), (<[k := l']> mdone).
    iFrame.
    iDestruct (own_slicemap_rep_move1 with "Hrep_todo Hrep_done") as "($&$)".
    { apply not_elem_of_dom. rewrite Hdom_done.
      apply map_disjoint_dom_1 in Hdisj.
      apply elem_of_dom_2 in Heq2.
      set_solver. }
    { eauto. }
    { eauto. }
    iSplit.
    { iPureIntro. rewrite union_delete_insert //. }
    iSplit.
    {
      iPureIntro.
      apply map_disjoint_dom_2.
      apply map_disjoint_dom_1 in Hdisj.
      rewrite dom_delete_L dom_insert_L. set_solver.
    }
    iPureIntro.
    rewrite marshalledMapSize_data_insert; last first.
    { apply not_elem_of_dom.
      apply map_disjoint_dom_1 in Hdisj.
      apply elem_of_dom_2 in Heq2.
      eauto. }
    rewrite Hsz'.
    transitivity (16 + uint.nat vsl.(Slice.sz) + uint.nat z)%nat.
    { lia. }
    rewrite Hnooverflow2. rewrite Hnooverflow1. word.
  }
  iIntros "(Hmap&Hinv)".
  iNamed "Hinv".
  iDestruct "Hinv" as "(?&?&%Hunion&%&?&%)".
  wp_pures.
  wp_apply (wp_LoadAt with "[$]").
  iIntros "Hs".
  iDestruct (own_slicemap_rep_empty_inv with "[$]") as %Hemp.
  assert (m = mdone) as Hdone.
  { rewrite Hemp left_id_L in Hunion. auto. }
  rewrite Hdone.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  rewrite /marshalledMapSize. word.
Qed.

Definition shard_own (mv : gmap u64 val) (m : gmap u64 (list u8)) id : iProp Σ :=
  ([∗ set] k ∈ fin_to_set u64, ⌜shardOfC k ≠ id ∧ mv !! k = None ∧ m !! k = None⌝
                               ∨ (∃ (vsl : Slice.t),
                                     ⌜default (slice_val Slice.nil) (mv !! k) = slice_val vsl⌝ ∗
                                             typed_slice.own_slice_small vsl byteT DfracDiscarded
                                             (default [] (m !! k)))).
(*
Lemma shard_own_shardOfC mv m id :
  shard_own mv m id -∗
  ⌜ (∀ k, k ∈ dom (gset _ ) m → shardOfC k = id) ⌝.
Proof.
  iIntros "H" (k Hin).
  rewrite /shard_own.
  iDestruct (big_sepS_elem_of _ _ k with "H") as "H".
  { apply elem_of_fin_to_set. }
  destruct (decide (shardOfC k = id)); auto.
  iDestruct "H" as "[H|H]".
  {
*)

Lemma shard_own_dup mv m id:
  shard_own mv m id -∗ shard_own mv m id ∗ shard_own mv m id.
Proof.
  iIntros "H".
  rewrite /shard_own. iApply big_sepS_sep.
  iApply (big_sepS_mono with "H").
  iIntros (x Hin) "H". iDestruct "H" as "[%Hl|Hr]".
  { iFrame "%". }
  iDestruct "Hr" as (vsl Heq) "#Hslice".
  iSplitL.
  { iRight. iExists _. iFrame. eauto. }
  { iRight. iExists _. iFrame. eauto. }
Qed.

Lemma shard_to_own_slicemap_rep (mv : gmap u64 val) m id:
  dom mv = dom m →
  ([∗ set] k ∈ fin_to_set u64, ⌜shardOfC k ≠ id ∧ mv !! k = None ∧ m !! k = None⌝
                               ∨ (∃ (vsl : Slice.t),
                                     ⌜default (slice_val Slice.nil) (mv !! k) = slice_val vsl⌝ ∗
                                             typed_slice.own_slice_small vsl byteT DfracDiscarded
                                             (default [] (m !! k)))) -∗
  own_slicemap_rep mv m.
Proof.
  iIntros (Hdom) "H".
  assert (dom mv ⊆ fin_to_set u64) as Hdomsub.
  { set_unfold. trivial. }
  remember (fin_to_set u64) as U eqn:Heq. clear Heq.
  iSplit; first done.
  iInduction mv as [| k v mv Hlookup] "IH" using map_ind forall (m U Hdom Hdomsub).
  { iApply big_sepM_empty. eauto. }
  iApply big_sepM_insert; eauto.
  iDestruct (big_sepS_delete _ _ k with "H") as "(Hk&H)".
  { rewrite dom_insert_L in Hdomsub. set_solver. }
  iDestruct ("IH" $! (delete k m) (U ∖ {[k]}) with "[] [] [H]") as "H".
  { iPureIntro.
    rewrite dom_insert_L in Hdom.
    rewrite dom_delete_L.
    rewrite -Hdom.
    apply not_elem_of_dom in Hlookup.
    set_solver. }
  { iPureIntro.
    rewrite dom_insert_L in Hdomsub.
    apply not_elem_of_dom in Hlookup.
    set_solver. }
  { iApply (big_sepS_mono with "H").
    iIntros (??) "H".
    rewrite lookup_insert_ne; last set_solver.
    rewrite lookup_delete_ne; last set_solver. eauto. }
  iSplitR "H".
  { iDestruct "Hk" as "[%Hbad|H]".
    { exfalso. rewrite lookup_insert in Hbad. intuition congruence. }
    rewrite lookup_insert. iDestruct "H" as (? Heq) "#H".
    iExists _. iSplit; first eauto. iFrame "∗#".
  }
  iApply (big_sepM_mono with "H").
  { iIntros (k' v' Hlookup').
    simpl. rewrite lookup_delete_ne; last set_solver. eauto. }
Qed.

Lemma wp_encodeInstallShardRequest args_ptr args :
  {{{
       own_InstallShardRequest args_ptr args
  }}}
    encodeInstallShardRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_InstallShardRequest reqData args⌝ ∗
                                               typed_slice.own_slice req_sl byteT (DfracOwn 1) reqData ∗
                                               own_InstallShardRequest args_ptr args
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  iDestruct (shard_own_dup with "Hvals") as "(Hvals&Hex)".
  iDestruct (shard_to_own_slicemap_rep with "Hex") as "Hslicemap".
  { eauto. }
  wp_loadField.
  wp_apply (wp_SizeOfMarshalledMap with "[$Hslicemap $HKvsMap]").
  iIntros (z) "(%Hsize&HKvsMap&Hslicemap)".
  wp_apply (wp_SumAssumeNoOverflow).
  iIntros (Hoverflow).
  wp_pures.
  wp_apply (wp_new_enc).
  iIntros (e) "Henc".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc").
  { rewrite Hoverflow. word. }
  iIntros "Henc".
  wp_pures.
  wp_loadField.
  wp_apply (wp_EncSliceMap with "[$Hslicemap $Henc $HKvsMap]").
  { rewrite Hoverflow. word. }
  iIntros (rmap) "(%Hhas&Hismap&Hslicemap&Henc)".
  wp_pures.
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (??) "(%&%&?)".
  iApply "HΦ".
  iFrame.
  iSplit; last eauto.
  iPureIntro. rewrite /has_encoding_InstallShardRequest. eexists; split; eauto.
Qed.

Definition DecSliceMap_invariant dec_v i_ptr m (r:Rec) mref s data : iProp Σ :=
  ∃ q (l:list (u64 * (list u8))) mdone' (mdone:gmap u64 (list u8)),
    ⌜NoDup l.*1⌝ ∗
    ⌜(list_to_map l) ##ₘ mdone⌝ ∗
    ⌜(list_to_map l) ∪ mdone = m⌝ ∗
    i_ptr ↦[uint64T] #(size mdone) ∗
    map.own_map mref (DfracOwn 1) (mdone', (slice_val Slice.nil)) ∗
    own_slicemap_rep mdone' mdone ∗
    is_dec dec_v
          ((flat_map (λ u : u64 * list u8, [EncUInt64 u.1; EncUInt64 (uint.Z (length u.2)); EncBytes u.2]) l) ++ r)
          s q data
.

Lemma is_dec_EncBytes_length d v r s q l :
  is_dec d (EncBytes v :: r) s q l  -∗
  ⌜uint.Z (length v) = length v⌝.
Proof.
  iNamed 1.
  apply has_encoding_length in Henc.
  rewrite ?encoded_length_cons encode1_bytes_len in Henc.
  iDestruct (typed_slice.own_slice_small_sz with "Hs") as %Hlen.
  iPureIntro.
  assert (length (drop (uint.nat off) l) <= length l).
  { rewrite drop_length. lia. }
  word.
Qed.

Lemma wp_DecSliceMap d l m args_sl argsData :
  NoDup l.*1 →
  uint.Z (size m) = size m →
  list_to_map l = m →
  {{{
      "Hdec" ∷ is_dec d
             ([EncUInt64 (size m)] ++
              flat_map (λ u : u64 * list u8, [EncUInt64 u.1; EncUInt64 (uint.Z (length u.2)); EncBytes u.2]) l)
             args_sl (DfracOwn 1) argsData
  }}}
    DecSliceMap d
  {{{
       rmap mv, RET #rmap;
       map.own_map rmap (DfracOwn 1) (mv, slice_val Slice.nil) ∗
       own_slicemap_rep mv m
  }}}.
Proof.
  iIntros (Hnodup Hsize Hlist).
  iIntros (Φ) "Hdec HΦ".
  wp_lam.
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_pures.
  wp_apply map.wp_NewMap.
  iIntros (mref) "Hmref".
  wp_pures.
  wp_apply (wp_ref_to); first eauto.
  iIntros (i_ptr) "Hi".
  wp_pures.
  iAssert (DecSliceMap_invariant d i_ptr m [] mref args_sl argsData) with "[Hi Hmref Hdec]" as "HloopInv".
  {
    iExists (DfracOwn 1), l, ∅, ∅.
    iFrame.
    iSplit; first done.
    iSplitL "".
    { iPureIntro. eapply (map_disjoint_empty_r (M:=gmap _)). }
    rewrite right_id.
    iSplit; first done.
    rewrite app_nil_r. iFrame.
    rewrite /own_slicemap_rep. rewrite ?dom_empty_L. rewrite big_sepM_empty //.
  }

  wp_forBreak_cond.
  clear Hlist Hnodup l.
  iDestruct "HloopInv" as (q l' mdone mdone' Hnodup Hdisj Hunion) "(Hi & Hmref & Hslicemap & Hdec)".
  wp_load.
  wp_pures.
  wp_if_destruct.
  { (* Start of loop iteration *)
    wp_pures.
    destruct l'.
    { simpl in Heqb. exfalso.
      simpl in *. rewrite left_id in Hunion.
      rewrite Hunion in Heqb. lia. }
    destruct p as [k v].
    simpl.
    wp_apply (wp_Dec__GetInt with "Hdec").
    iIntros "Hdec".
    wp_apply (wp_Dec__GetInt with "Hdec").
    iIntros "Hdec".
    iDestruct (is_dec_EncBytes_length with "Hdec") as %Hlen_dec.
    wp_apply (wp_Dec__GetBytes with "Hdec").
    { word. }
    iIntros (q' s') "(Hsl&Hdec)".
    iMod (own_slice_small_persist with "Hsl") as "#Hsl".
    wp_pures.
    wp_apply (map.wp_MapInsert with "Hmref").
    iIntros "Hmref".
    wp_pures.
    wp_load.
    wp_store.
    iLeft.
    iSplitL ""; first done.
    iSplitL "HΦ"; first done.
    iExists q', l', _,  (<[k:=v]> mdone').
    iFrame "Hmref".
    iModIntro.
    iSplitL "".
    { by apply NoDup_cons in Hnodup as [??]. }
    assert ((list_to_map l' (M:=gmap _ _)) !! k = None) as Hnok.
    { apply NoDup_cons in Hnodup as [HkNotInL Hnodup].
        by apply not_elem_of_list_to_map_1. }
    iFrame.
    iSplitL "".
    { iPureIntro. simpl in Hdisj.
      rewrite map_disjoint_insert_r.
      split; first done.
      eapply map_disjoint_weaken; eauto.
      simpl.
      apply insert_subseteq.
      done.
    }
    iSplitL "".
    { iPureIntro. simpl in Hunion.
      rewrite -insert_union_r; last done.
      rewrite insert_union_l.
      done.
    }
    rewrite (map_size_insert_None); last first.
    { eapply map_disjoint_Some_l; eauto.
      simpl. apply lookup_insert. }
    replace (word.add (size mdone') 1) with (uint.Z (size mdone') + 1:u64) by word.
    rewrite Z_u64; last first.
    { split; first lia.
      word_cleanup.
      rewrite Hsize in Heqb.
      assert (size mdone' ≤ size m)%nat.
      { rewrite -Hunion.
        rewrite ?Map.map_size_dom.
        apply subseteq_size. set_solver. }
      lia.
    }
    replace (Z.of_nat (S (size mdone'))) with (size mdone' + 1)%Z by lia.
    iFrame.
    rewrite /own_slicemap_rep.
    iNamed "Hslicemap".
    iSplit.
    { rewrite ?dom_insert_L; iPureIntro; congruence. }
    assert (mdone !! k = None).
    { apply not_elem_of_dom. rewrite Hmdoms.
      rewrite list_to_map_cons in Hdisj.
      apply map_disjoint_dom_1 in Hdisj.
      rewrite dom_insert_L in Hdisj. set_solver.
    }
    iApply big_sepM_insert; first auto.
    iSplitL "Hsl".
    { iExists _. iSplit; first eauto.
      rewrite lookup_insert //=. }
    iApply (big_sepM_mono with "Hmvals").
    iIntros (k' x' Hlookup).
    simpl. rewrite lookup_insert_ne //.
    intros Heq. subst. congruence.
  }
  assert (size mdone' ≤ size m)%nat.
  { rewrite -Hunion.
    rewrite ?Map.map_size_dom.
    apply subseteq_size. set_solver. }
  iRight. iSplitL ""; first done.
  iModIntro.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
  destruct l'; last first.
  {
    exfalso.
    set (mtodo:=(list_to_map (p :: l'))) in *.
    assert (size m <= size mdone').
    { rewrite ?Z_u64 in Heqb; try word. }
    rewrite -Hunion in Heqb.
    rewrite map_size_disj_union in Heqb; eauto.
    assert (size mtodo > 0).
    { destruct (decide (size mtodo = O)) as [Hz|Hnz]; try lia.
      rewrite ?Map.map_size_dom in Hz.
      apply size_empty_inv in Hz.
      apply dom_empty_inv in Hz.
      rewrite /mtodo in Hz.
      destruct p. rewrite list_to_map_cons in Hz.
      apply insert_non_empty in Hz. exfalso; eauto.
    }
    assert (size m = size mtodo + size mdone')%nat.
    { rewrite -Hunion map_size_disj_union; eauto. }
    word.
  }
  rewrite list_to_map_nil left_id_L in Hunion. subst. iFrame.
Qed.

Lemma own_slicemap_rep_to_shard (mv : gmap u64 val) m id:
  own_slicemap_rep mv m -∗
  ([∗ set] k ∈ fin_to_set u64, ⌜shardOfC k ≠ id ∧ mv !! k = None ∧ m !! k = None⌝
                               ∨ (∃ (vsl : Slice.t),
                                     ⌜default (slice_val Slice.nil) (mv !! k) = slice_val vsl⌝ ∗
                                             typed_slice.own_slice_small vsl byteT DfracDiscarded
                                             (default [] (m !! k)))).
Proof.
  iInduction mv as [| k v mv Hlookup] "IH" using map_ind forall (m).
  { iNamed 1. iApply big_sepS_intro.
    iIntros "!>" (?) "?". iRight.
    assert (m = ∅) as ->.
    { apply dom_empty_inv_L. rewrite dom_empty_L in Hmdoms. congruence. }
    rewrite ?lookup_empty /=.
    iExists _. iSplit; first eauto.
    iApply (@typed_slice.own_slice_to_small with "[]").
    iApply typed_slice.own_slice_zero.
  }
  iNamed 1. iDestruct (big_sepM_insert with "Hmvals") as "(Hk&Hmvals)"; auto.
  iDestruct ("IH" $! (delete k m) with "[Hmvals]") as "Hrest".
  { iSplit; first iPureIntro.
    { rewrite dom_insert_L in Hmdoms.
      rewrite dom_delete_L.
      apply not_elem_of_dom in Hlookup.
      set_solver. }
    iApply (big_sepM_mono with "Hmvals").
    { iIntros (k' x' Hlookup') "H".
      rewrite lookup_delete_ne; eauto. congruence. }
  }
  iApply (big_sepS_delete _ _ k); first apply elem_of_fin_to_set.
  iDestruct (big_sepS_delete _ _ k with "Hrest") as "(_&Hrest)"; first apply elem_of_fin_to_set.
  iSplitL "Hk".
  { iRight. rewrite lookup_insert. iDestruct "Hk" as (? Heq) "H". iExists _. iSplit; eauto. }
  iApply (big_sepS_mono with "Hrest").
  { iIntros (??) "H".
    rewrite lookup_insert_ne; last by set_solver.
    rewrite lookup_delete_ne; last by set_solver.
    eauto.
  }
Qed.

Lemma wp_decodeInstallShardRequest args args_sl argsData :
  {{{
       typed_slice.own_slice_small args_sl byteT (DfracOwn 1) argsData ∗
       ⌜has_encoding_InstallShardRequest argsData args ⌝
  }}}
    decodeInstallShardRequest (slice_val args_sl)
  {{{
       (args_ptr:loc), RET #args_ptr;
       own_InstallShardRequest args_ptr args
  }}}.
Proof.
  iIntros (Φ) "(Hslice&%Henc) HΦ".
  wp_lam.
  destruct Henc as (r&(l&Hsize&Hnodup&HlistMap&Hmapencoded)&Hdata).
  rewrite Hmapencoded in Hdata.
  wp_apply (wp_new_dec with "Hslice"); eauto.
  iIntros (d) "Hdec".
  wp_pures.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (req) "Hreq".
  wp_pures.
  iDestruct (struct_fields_split with "Hreq") as "H".
  iNamed "H".
  wp_apply (wp_Dec__GetInt with "Hdec").
  iIntros "Hdec".
  wp_storeField.
  wp_apply (wp_DecSliceMap with "[$]"); try eauto.
  iIntros (rmap mv) "(Hmref&Hslicemap)".
  wp_storeField.
  iModIntro.
  iApply "HΦ".
  iExists _, _. iFrame.
  iDestruct (own_slicemap_rep_dom with "[$]") as "%Hdom".
  iSplit; auto.
  iApply own_slicemap_rep_to_shard. eauto.
Qed.

End memkv_marshal_install_shard_proof.
