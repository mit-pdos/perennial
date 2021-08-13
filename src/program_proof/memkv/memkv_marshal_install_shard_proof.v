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

Definition marshalledMapSize (m:gmap u64 (list u8)) : nat := 8 + 8 * 2 * (size m).

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
    ⌜8 * 2 * (size mtodo) ≤ remaining⌝ ∗
    ⌜remaining = original_remaining - 8 * 2 * (size mdone)⌝ ∗
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
    iPureIntro. split; first by lia.
    rewrite dom_empty_L.
    replace (size ∅) with (0%nat).
    { split; first by lia. apply map_disjoint_empty_r. }
    symmetry. rewrite size_empty //.
  }
  {
    clear Φ.
    iIntros (?? mtodo' mdone' Φ) "!# [Hpre %Htodo] HΦ".
    wp_pures.
    iDestruct "Hpre" as (mtodo mdone l rem') "Hpre".
    iDestruct "Hpre" as "(Hrep_todo&Hrep_done&Hpre)".
    iDestruct "Hpre" as (Hnodup Hl Hrem' Hremeq Hmdisjoint) "Henc".
    iDestruct (is_slicemap_rep_dom with "Hrep_todo") as %Hdom_todo.

    assert (size mtodo ≠ 0%nat).
    { apply map_size_non_empty_iff.
      intros Heq. rewrite Heq dom_empty_L in Hdom_todo.
      apply elem_of_dom_2 in Htodo. set_solver.
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
Abort.
(*
    iApply "HΦ".
    iExists (l ++ [(k, v)]), (rem' - 8 - 8).
    iSplit.
    { iPureIntro.
      rewrite fmap_app.
      rewrite NoDup_app.
      split; first done.
      split.
      { intros.
        simpl.
        rewrite not_elem_of_cons.
        split; last apply not_elem_of_nil.
        destruct (decide (x = k)) as [->|]; last done.
        exfalso.
        apply elem_of_list_fmap_2 in H1 as [ [k0 v0] [Hk Hp]].
        simpl in Hk.
        eapply (elem_of_list_to_map_1 (M:=gmap _)) in Hnodup; eauto.
        replace (list_to_map l) with (mdone) in Hnodup by eauto.
        eapply map_disjoint_spec; eauto.
        by rewrite Hk.
      }
      { apply NoDup_cons_2.
        - apply not_elem_of_nil.
        - apply NoDup_nil_2.
      }
    }
    iSplit.
    { iPureIntro.
      rewrite -Hl.
      apply list_to_map_snoc.
      (* XXX: had to put the M there because typeclass resolution was not working well *)
      rewrite (not_elem_of_list_to_map (M:=(@gmap u64 u64_eq_dec u64_countable))).
      rewrite Hl.
      destruct (mdone !! k) eqn:Hcase; last done.
      exfalso; by eapply map_disjoint_spec.
    }
    iSplit.
    { replace (size (delete k mtodo)) with (pred (size mtodo)).
      { iPureIntro. lia. }
      { symmetry. apply map_size_delete_Some. eauto. }
    }
    rewrite flat_map_app.
    simpl.
    replace ([EncUInt64 k; EncUInt64 v]) with ([EncUInt64 k] ++ [EncUInt64 v]) by eauto.
    iFrame.
    rewrite -app_assoc.
    rewrite -app_assoc.
    iFrame.
    iPureIntro.

    destruct (mdone !! k) eqn:X.
    - exfalso. eapply map_disjoint_spec; eauto.
    - split.
      + rewrite map_size_insert_None; first lia. done.
      + apply map_disjoint_insert_r_2.
        { apply lookup_delete. }
        by apply map_disjoint_delete_l.
  }
  iIntros "[Hmap Henc]".
  iDestruct "Henc" as (l rem' Hnodup Hl _ ? ?) "Henc".
  iApply ("HΦ" $! (
              [EncUInt64 (size m)] ++
              flat_map (λ u : u64 * u64, [EncUInt64 u.1; EncUInt64 u.2]) l)
         ).
  iFrame "Hmap".
  unfold marshalledMapSize.
  replace (remaining - (8 + 8 * 2 * size m)%nat) with (rem') by lia.
  iFrame.
  iPureIntro.
  exists l.
  rewrite -u64_Z_through_nat.
  eauto.
Qed.
*)


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
