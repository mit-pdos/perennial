From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof Require Import marshal_proof.

(*
  Defines Coq request and reply types for shard server Get RPC. Also defines
  has_encoding for Get Request/Reply and provides WPs for {de|en}codeGetRe{ply|quest}()
 *)

Section memkv_marshal_get_proof.

Context `{!heapG Σ}.

Record GetRequestC := mkGetRequestC {
  GR_CID : u64;
  GR_Seq : u64;
  GR_Key : u64
}.

Record GetReplyC := mkGetReplyC {
  GR_Err : u64;
  GR_Value : list u8
}.

Definition own_GetRequest args_ptr args : iProp Σ :=
  "HCID" ∷ args_ptr ↦[GetRequest :: "CID"] #args.(GR_CID) ∗
  "HSeq" ∷ args_ptr ↦[GetRequest :: "Seq"] #args.(GR_Seq) ∗
  "HKey" ∷ args_ptr ↦[GetRequest :: "Key"] #args.(GR_Key) ∗
  "%HseqPositive" ∷ ⌜int.Z args.(GR_Seq) > 0⌝
.

Definition own_GetReply reply_ptr rep : iProp Σ :=
  ∃ val_sl,
  "HErr" ∷ reply_ptr ↦[GetReply :: "Err"] #rep.(GR_Err) ∗
  "HValue" ∷ reply_ptr ↦[GetReply :: "Value"] (slice_val val_sl) ∗
  "HValue_sl" ∷ ∃ (q:Qp), (typed_slice.is_slice_small val_sl byteT q rep.(GR_Value))
.

Definition has_encoding_GetRequest (data:list u8) (args:GetRequestC) :=
  has_encoding data [ EncUInt64 args.(GR_CID) ; EncUInt64 args.(GR_Seq) ; EncUInt64 args.(GR_Key) ] ∧
  int.Z args.(GR_Seq) > 0.

Definition has_encoding_GetReply (data:list u8) (rep:GetReplyC) :=
  has_encoding data [ EncUInt64 rep.(GR_Err) ; EncUInt64 (length rep.(GR_Value)) ; EncBytes rep.(GR_Value) ] ∧
  length rep.(GR_Value) = int.nat (length rep.(GR_Value)).

Lemma wp_encodeGetRequest args_ptr args :
  {{{
       own_GetRequest args_ptr args
  }}}
    encodeGetRequest #args_ptr
  {{{
       (reqData:list u8) req_sl, RET (slice_val req_sl); ⌜has_encoding_GetRequest reqData args⌝ ∗
                                               typed_slice.is_slice req_sl byteT 1%Qp reqData ∗
                                               own_GetRequest args_ptr args
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_apply (wp_new_enc).
  iIntros (?) "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "[$Henc]").
  { done. }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "[$Henc]").
  { done. }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "[$Henc]").
  { done. }
  iIntros "Henc".
  wp_pures.

  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (??) "(%Henc & Hlen & Hsl)".
  iApply "HΦ".
  iFrame.
  done.
Qed.

Lemma wp_decodeGetRequest req_sl reqData args :
  {{{
       ⌜has_encoding_GetRequest reqData args⌝ ∗
       typed_slice.is_slice req_sl byteT 1%Qp reqData
  }}}
    decodeGetRequest (slice_val req_sl)
  {{{
       (args_ptr:loc), RET #args_ptr; own_GetRequest args_ptr args
  }}}.
Proof.
  iIntros (Φ) "[[%Henc %] Hsl] HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  {
    naive_solver.
  }
  iIntros (rep_ptr) "Hrep".
  iDestruct (struct_fields_split with "Hrep") as "HH".
  iNamed "HH".
  wp_pures.
  iDestruct (typed_slice.is_slice_small_acc with "Hsl") as "[Hsl _]".
  wp_apply (wp_new_dec with "[$Hsl]").
  { done. }
  iIntros (?) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  iApply "HΦ". iModIntro. by iFrame.
Qed.

Lemma wp_decodeGetReply rep rep_sl repData :
  {{{
       typed_slice.is_slice rep_sl byteT 1%Qp repData ∗
       ⌜has_encoding_GetReply repData rep ⌝
  }}}
    decodeGetReply (slice_val rep_sl)
  {{{
       (rep_ptr:loc) , RET #rep_ptr;
       own_GetReply rep_ptr rep
  }}}.
Proof.
  iIntros (Φ) "[Hsl %Henc] HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  {
    rewrite zero_slice_val.
    naive_solver.
  }
  iIntros (rep_ptr) "Hrep".
  iDestruct (struct_fields_split with "Hrep") as "HH".
  iNamed "HH".
  wp_pures.
  iDestruct (typed_slice.is_slice_small_acc with "Hsl") as "[Hsl _]".
  destruct Henc as [Henc Hsz].
  wp_apply (wp_new_dec with "[$Hsl]").
  { done. }
  iIntros (?) "Hdec".
  wp_pures.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_storeField.

  wp_apply (wp_Dec__GetInt with "[$Hdec]").
  iIntros "Hdec".
  wp_apply (wp_Dec__GetBytes with "[$Hdec]").
  { done. }
  iIntros (??) "[Hsl Hdec]".
  wp_apply (wp_storeField with "Value").
  { apply slice_val_ty. }
  iIntros "Value".
  wp_pures.
  iApply "HΦ".
  iModIntro.
  iExists _.
  iFrame.
  iExists _; iFrame.
Qed.

Local Lemma nooverflow (x y : u64) :
  int.Z y < int.Z (word.add x y) →
  int.Z (word.add x y) = (int.Z x) + (int.Z y).
Proof.
  intros. word_cleanup. rewrite wrap_small //.
  assert (0 ≤ int.Z (word.add x y) < 2 ^ 64) by admit.
  Fail word.
Admitted.

Lemma wp_encodeGetReply rep_ptr rep :
  {{{
       own_GetReply rep_ptr rep
  }}}
    encodeGetReply #rep_ptr
  {{{
       repData rep_sl , RET (slice_val rep_sl);
       typed_slice.is_slice rep_sl byteT 1%Qp repData ∗
       ⌜has_encoding_GetReply repData rep ⌝
  }}}.
Proof.
  iIntros (Φ) "Hrep HΦ".

  wp_lam.
  wp_pures.
  iNamed "Hrep".
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.

  wp_loadField.
  wp_apply (wp_slice_len).
  wp_apply (wp_Assume).
  rewrite bool_decide_eq_true.
  iIntros (Hoverflow).

  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutInt with "Henc").
  { (* For some reason, having the negation in the context helps word -- but not if the goal is already False! *)
    apply dec_stable. intros HP. apply HP. word.
  }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  iDestruct "HValue_sl" as (?) "HValue_sl".
  iDestruct (typed_slice.is_slice_small_sz with "HValue_sl") as %Hsz.
  wp_apply (wp_slice_len).
  wp_apply (wp_Enc__PutInt with "Henc").
  { apply dec_stable. intros HP. apply HP. word. }
  iIntros "Henc".
  wp_pures.

  wp_loadField.
  wp_apply (wp_Enc__PutBytes with "[$Henc $HValue_sl]").
  { apply nooverflow in Hoverflow.
    rewrite Hoverflow Hsz.
    change (int.Z (word.add 8 8)) with 16.
    rewrite Z2Nat.id; word. }
  iIntros "[Henc Hsl]".
  wp_pures.
  wp_apply (wp_Enc__Finish with "[$Henc]").
  iIntros (rep_sl repData).
  iIntros "(% & % & Hrep_sl)".
  iApply "HΦ".
  iFrame.
  iDestruct (typed_slice.is_slice_small_sz with "Hsl") as %Hsz2.
  iPureIntro.
  unfold has_encoding_GetReply.
  rewrite Hsz.
  assert (U64 (int.nat (Slice.sz val_sl)) = (Slice.sz val_sl)).
  { word. }
  rewrite H1.
  rewrite app_nil_l in H.
  simpl in H.
  done.
Qed.

End memkv_marshal_get_proof.
