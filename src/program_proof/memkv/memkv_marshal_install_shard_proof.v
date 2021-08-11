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
  r = [EncUInt64 (size m)] ++ (EncUInt64 (size m) :: ((flat_map (λ u, [EncUInt64 u.1 ; EncBytes u.2]) l))).

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

(* TODO: need a hypothesis about correspondence between mv and m *)
Lemma wp_EncSliceMap e mref mv m sz r remaining :
marshalledMapSize m <= remaining →
{{{
    "HKvsMap" ∷ map.is_map mref 1 (mv, slice_val Slice.nil) ∗
    "Henc" ∷ is_enc e sz r remaining
}}}
  EncSliceMap e #mref
{{{
     rmap, RET #();
     ⌜has_byte_map_encoding m rmap⌝ ∗
     map.is_map mref 1 (mv, slice_val Slice.nil) ∗
     is_enc e sz (r ++ rmap) (remaining - marshalledMapSize m)
}}}.
Proof using Type*.
Abort.
(* TODO: this is copy + pasted from the old EncMap in kv_durable, probably hardly works *)
(*
  intros Hrem.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam. wp_pures.

  wp_apply (wp_MapLen with "Hmap").
  iIntros "[%Hsize Hmap]".
  unfold marshalledMapSize in Hrem.
  wp_apply (wp_Enc__PutInt with "Henc").
  { lia. }
  iIntros "Henc".
  wp_pures.
  wp_apply (wp_MapIter_2 _ _ _ _ (EncMap_invariant e r sz (size m) (remaining - 8)) with "Hmap [Henc] [] [HΦ]").
  {
    iExists [] . iExists (remaining-8). simpl. iFrame.
    iSplit.
    { iPureIntro. apply NoDup_nil_2. }
    iSplit; first done.
    iPureIntro. split; first by lia.
    replace (size ∅) with (0%nat).
    { split; first by lia. apply map_disjoint_empty_r. }
    symmetry. by apply map_size_empty_iff.
  }
  {
    clear Φ.
    iIntros (???? Φ) "!# [Hpre %Htodo] HΦ".
    wp_pures.
    iDestruct "Hpre" as (l rem' Hnodup Hl Hrem' Hremeq Hmdisjoint) "Henc".

    assert (size mtodo ≠ 0%nat).
    { apply map_size_non_empty_iff.
      destruct (bool_decide (mtodo = ∅)) as [|] eqn:X.
      { apply bool_decide_eq_true in X. rewrite X in Htodo. done. }
      { by apply bool_decide_eq_false in X. }
    }
    wp_apply (wp_Enc__PutInt with "Henc").
    {
      lia.
    }
    iIntros "Henc".
    wp_pures.

    wp_apply (wp_Enc__PutInt with "Henc").
    {
      lia.
    }
    iIntros "Henc".
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
