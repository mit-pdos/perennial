From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Export marshal_proof memkv.common_proof.

(*
  Defines Coq request and reply types for shard server InstallShard RPC. Also defines
  has_encoding for InstallShard Request/Reply and provides WPs for {de|en}codeInstallShardRe{ply|quest}()
 *)

Section memkv_marshal_install_shard_proof.

Record InstallShardRequestC := mkInstallShardC {
  IR_CID : u64;
  IR_Seq : u64;
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
  (int.Z (size m) = size m) ∧
  NoDup l.*1 ∧
  (list_to_map l) = m ∧
  r = [EncUInt64 (size m)] ++
      ((flat_map (λ u, [EncUInt64 u.1 ; EncUInt64 (int.Z (length (u.2))); EncBytes u.2]) l)).

Definition has_encoding_InstallShardRequest (data:list u8) (args:InstallShardRequestC) : Prop :=
  ∃ r, has_byte_map_encoding (args.(IR_Kvs)) r ∧
       has_encoding data ([EncUInt64 args.(IR_CID); EncUInt64 args.(IR_Seq); EncUInt64 args.(IR_Sid)] ++ r).

(*
Definition has_encoding_InstallShardRequest (data:list u8) (args:InstallShardRequestC) : Prop :=
  ∃ l,
   let m := args.(IR_Kvs) in
  (int.Z (size m) = size m) ∧
  NoDup l.*1 ∧
  (list_to_map l) = m ∧
  has_encoding data ([EncUInt64 args.(IR_CID); EncUInt64 args.(IR_Seq); EncUInt64 args.(IR_Sid)] ++
                    (EncUInt64 (size m) :: ((flat_map (λ u, [EncUInt64 u.1 ; EncBytes u.2]) l)))).
*)

Context `{!heapGS Σ}.

Definition is_slicemap_rep (mv : gmap u64 val) (m : gmap u64 (list u8)) : iProp Σ :=
  "%Hmdoms" ∷ ⌜ dom (gset _) mv = dom (gset _) m ⌝ ∗
  "Hmvals" ∷ ([∗ map] k ↦ v ∈ mv, (∃ (q : Qp) vsl, ⌜ v = slice_val vsl ⌝ ∗
              typed_slice.is_slice_small vsl byteT q (default [] (m !! k))))%I.

Lemma is_slicemap_rep_dom  mv m :
  is_slicemap_rep mv m -∗ ⌜ dom (gset _) mv = dom (gset _) m ⌝.
Proof. iIntros "($&_)". Qed.

Lemma is_slicemap_rep_dup mv m :
  is_slicemap_rep mv m -∗ is_slicemap_rep mv m ∗ is_slicemap_rep mv m.
Proof.
  iIntros "Hrep".
  rewrite /is_slicemap_rep.
  iNamed "Hrep". iFrame "%".
  rewrite -big_sepM_sep.
  iApply (big_sepM_mono with "Hmvals").
  iIntros (k x Hlookup) "H".
  iDestruct "H" as (q vsl Heq) "Hslice".
  rewrite -(Qp_div_2 q).
  iDestruct (fractional.fractional_split_1 with "Hslice") as "[Hl1 Hl2]".
  iSplitL "Hl1".
  { iExists _, _. iFrame. eauto. }
  { iExists _, _. iFrame. eauto. }
Qed.


Lemma is_slicemap_rep_move1 m1 m1' m2 m2' k l l':
  m2 !! k = None →
  m1 !! k = Some l →
  m1' !! k = Some l' →
  is_slicemap_rep m1 m1' -∗
  is_slicemap_rep m2 m2' -∗
  (is_slicemap_rep (delete k m1) (delete k m1') ∗
   is_slicemap_rep (<[k := l]> m2) (<[k := l']> m2')).
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
    { iIntros (?? Hldel) "H". iDestruct "H" as (?? Heq) "H". iExists _, _. iFrame "%".
      rewrite lookup_delete_ne //.
      intros Heq'. rewrite Heq' lookup_delete in Hldel. congruence. }
  }
  iSplit; first iPureIntro.
  { rewrite ?dom_insert_L; congruence. }
  iApply (big_sepM_insert_2 with "[Hl]"); auto.
  { simpl. iDestruct "Hl" as (?? Heql) "H". iExists _, _. iFrame "%".
    rewrite lookup_insert. rewrite Hl'. eauto. }
  iApply (big_sepM_mono with "Hmvals2").
  { iIntros (k' ? Hldel) "H". iDestruct "H" as (?? Heq) "H". iExists _, _. iFrame "%".
    destruct (decide (k = k')).
    { subst. congruence. }
    rewrite lookup_insert_ne //.
  }
Qed.

Lemma is_slicemap_lookup_l mv m k v :
  mv !! k = Some v →
  is_slicemap_rep mv m -∗
  is_slicemap_rep mv m ∗
  ∃ q vsl l, ⌜ v = slice_val vsl ⌝ ∗ ⌜ m !! k = Some l ⌝ ∗
   typed_slice.is_slice_small vsl byteT q l.
Proof.
  iIntros (Hlookup) "Hrep".
  iDestruct (is_slicemap_rep_dup with "Hrep") as "(Hrep&$)".
  iNamed "Hrep".
  iDestruct (big_sepM_lookup with "Hmvals") as (q vsl Heq) "H"; eauto.
  assert (is_Some (m !! k)) as (l&Heq').
  { apply elem_of_dom_2 in Hlookup. rewrite Hmdoms in Hlookup. apply elem_of_dom in Hlookup. eauto. }
  iExists q, vsl, l. iFrame "%". rewrite Heq' //.
Qed.

Definition EncSliceMap_invariant enc_v (r:Rec) sz map_sz
           (original_remaining:Z) (mtodo' mdone':gmap u64 val) : iProp Σ :=
  ∃ mtodo mdone (l:list (u64 * (list u8))) (remaining:Z),
    is_slicemap_rep mtodo' mtodo ∗
    is_slicemap_rep mdone' mdone ∗
    ⌜ NoDup l.*1 ⌝ ∗
    ⌜(list_to_map l) = mdone⌝ ∗
    ⌜marshalledMapSize_data mtodo ≤ remaining⌝ ∗
    ⌜remaining = (original_remaining - marshalledMapSize_data mdone)%Z⌝ ∗
    ⌜mtodo ##ₘ mdone ⌝ ∗
    is_enc enc_v sz (r ++ [EncUInt64 map_sz] ++
 (flat_map (λ u, [EncUInt64 u.1 ; EncUInt64 (int.Z (length (u.2))); EncBytes u.2]) l )) remaining
.

(*
Definition EncSliceMap_invariant enc_v (r:Rec) sz map_sz
           (original_remaining:Z) (mtodo mdone:gmap u64 (list u8)) : iProp Σ :=
  ∃ (l:list (u64 * (list u8))) (remaining:Z),
    ⌜ NoDup l.*1 ⌝ ∗
    ⌜(list_to_map l) = mdone⌝ ∗
    ⌜8 * 2 * (size mtodo) ≤ remaining⌝ ∗
    ⌜remaining = original_remaining - 8 * 2 * (size mdone)⌝ ∗
    ⌜mtodo ##ₘ mdone ⌝ ∗
    is_enc enc_v sz (r ++ [EncUInt64 map_sz] ++ (flat_map (λ u, [EncUInt64 u.1 ; EncBytes u.2]) l )) remaining
.
*)



Definition own_InstallShardRequest args_ptr args : iProp Σ :=
  ∃ (kvs_ptr:loc) (mv:gmap u64 goose_lang.val),
  "HCID" ∷ args_ptr ↦[InstallShardRequest :: "CID"] #args.(IR_CID) ∗
  "HSeq" ∷ args_ptr ↦[InstallShardRequest :: "Seq"] #args.(IR_Seq) ∗
  "HKey" ∷ args_ptr ↦[InstallShardRequest :: "Sid"] #args.(IR_Sid) ∗
  "HKvs" ∷ args_ptr ↦[InstallShardRequest :: "Kvs"] #kvs_ptr ∗
  "HKvsMap" ∷ map.is_map kvs_ptr 1 (mv, (slice_val Slice.nil)) ∗
  "%HseqPositive" ∷ ⌜int.Z args.(IR_Seq) > 0⌝ ∗
  "Hvals" ∷ ([∗ set] k ∈ (fin_to_set u64),
        ⌜shardOfC k ≠ args.(IR_Sid) ∧ mv !! k = None ∧ args.(IR_Kvs) !! k = None⌝ ∨ (∃ q vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.is_slice_small vsl byteT q (default [] (args.(IR_Kvs) !! k))) )
.

Lemma wp_EncSliceMap e mref mv m sz r remaining :
marshalledMapSize m <= remaining →
{{{
    "HKvsMap" ∷ map.is_map mref 1 (mv, slice_val Slice.nil) ∗
    "Henc" ∷ is_enc e sz r remaining ∗
    "Hvals" ∷ is_slicemap_rep mv m
}}}
  EncSliceMap e #mref
{{{
     rmap, RET #();
     ⌜has_byte_map_encoding m rmap⌝ ∗
     map.is_map mref 1 (mv, slice_val Slice.nil) ∗
     is_slicemap_rep mv m ∗
     is_enc e sz (r ++ rmap) (remaining - marshalledMapSize m)
}}}.
Proof using Type*.
  intros Hrem.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam. wp_pures.

  wp_apply (map.wp_MapLen with "HKvsMap").
  iIntros "[%Hsize Hmap]".
  unfold marshalledMapSize in Hrem.
  wp_apply (wp_Enc__PutInt with "Henc").
  { lia. }
  iIntros "Henc".
  wp_pures.
  wp_apply (map.wp_MapIter_2 _ _ _ _ _ (EncSliceMap_invariant e r sz (size m) (remaining - 8))
              with "Hmap [Henc Hvals] [] [HΦ]").
  {
    iDestruct (is_slicemap_rep_dom with "[$]") as %Hdom.
    iExists m, ∅.
    iExists []. iExists (remaining-8). simpl. iFrame.
    iSplitL "".
    { rewrite /is_slicemap_rep. rewrite ?dom_empty_L big_sepM_empty //=. }
    iSplit.
    { iPureIntro. apply NoDup_nil_2. }
    iSplit; first done.
    rewrite ?Map.map_size_dom Hdom //.
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
    iDestruct "Hpre" as (Hnodup Hl Hrem' Hremeq Hmdisjoint) "Henc".
    iDestruct (is_slicemap_rep_dom with "Hrep_todo") as %Hdom_todo.
    iDestruct (is_slicemap_rep_dom with "Hrep_done") as %Hdom_done.
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

    iDestruct (is_slicemap_lookup_l with "Hrep_todo") as "(Hrep_todo&Hval)"; eauto.
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
    assert (k ∉ dom (gset u64) (list_to_map l : gmap u64 (list u8))).
    { intros Hin. apply map_disjoint_dom_1 in Hmdisjoint.
      apply elem_of_dom_2 in Heq2. eauto. }
    iDestruct (is_slicemap_rep_move1 with "Hrep_todo Hrep_done") as "($&$)".
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
    iDestruct (typed_slice.is_slice_small_sz with "Hslice") as %Hsz'.
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
  iApply ("HΦ" $! ([EncUInt64 (size m)] ++
                 flat_map (λ u : u64 * list u8, [EncUInt64 u.1; EncUInt64 (int.Z (length u.2)); EncBytes u.2]) l)).
  iDestruct "Hinv" as "(?&?&?&?&?&->&?&Henc)".
  iFrame.
  rewrite /marshalledMapSize.
  iSplit.
  { admit. }
  iSplitR "Henc"; last first.
  { iExactEq "Henc". f_equal.
    (* Need to strengthen EncMap invariant to say that mtodo ∪ mdone is the original map,
       so that at end when we know mtodo = ∅, we can deduce mdone = m *)
Abort.

Lemma wp_encodeInstallShardRequest args_ptr args :
  {{{
       own_InstallShardRequest args_ptr args
  }}}
    encodeInstallShardRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_InstallShardRequest reqData args⌝ ∗
                                               typed_slice.is_slice req_sl byteT 1%Qp reqData ∗
                                               own_InstallShardRequest args_ptr args
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_loadField.
  wp_pures.
  rewrite /SizeOfMarshalledMap.
  (*
  wp_apply (wp_SumAssumeNoOverflow).
  iIntros (?) "Henc".
  wp_pures.
   *)
Admitted.

Lemma wp_decodeInstallShardRequest args args_sl argsData :
  {{{
       typed_slice.is_slice args_sl byteT 1%Qp argsData ∗
       ⌜has_encoding_InstallShardRequest argsData args ⌝
  }}}
    decodeInstallShardRequest (slice_val args_sl)
  {{{
       (args_ptr:loc), RET #args_ptr;
       own_InstallShardRequest args_ptr args
  }}}.
Proof.
Admitted.

End memkv_marshal_install_shard_proof.
