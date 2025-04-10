From Perennial.program_proof Require Import grove_prelude.
From Perennial Require Import base.
From Goose.github_com.mit_pdos.pav Require Import marshalutil.

From Perennial.program_proof Require Import marshal_stateless_proof.

Section wps.
Context `{!heapGS Σ}.

Definition read_bool (b0 : list w8) : (bool * list w8 * bool) :=
  match b0 with
  | [] => (false, [], true)
  | a :: l => (bool_decide (uint.Z a ≠ 0), l, false)
  end.

Lemma wp_ReadBool b0_sl dq (b0 : list w8) :
  let '(v, b, err) := read_bool b0 in
  {{{ own_slice_small b0_sl byteT dq b0 }}}
    ReadBool (slice_val b0_sl)
  {{{
        sl, RET (#v, slice_val sl, #err);
        own_slice_small sl byteT dq b
  }}}.
Proof.
  destruct b0; intros ?.
  - iIntros "Hpre HΦ".
    wp_rec. wp_apply wp_ref_to; [val_ty|].
    iIntros (?) "Hb_ptr". wp_pures.
    iDestruct (own_slice_small_sz with "[$]") as %Hsz.
    wp_load. wp_apply wp_slice_len. wp_pures.
    simpl in *. rewrite -> bool_decide_true by word. wp_pures.
    replace (slice.nil) with (slice_val Slice.nil) by done.
    iApply "HΦ". iApply own_slice_small_nil. done.
  - iIntros "Hpre HΦ".
    wp_rec. wp_apply wp_ref_to; [val_ty|].
    iIntros (?) "Hb_ptr". wp_pures.
    iDestruct (own_slice_small_sz with "[$]") as %Hsz.
    wp_load. wp_apply wp_slice_len. wp_pures.
    simpl in *. rewrite -> (bool_decide_false (_ < _)) by word. wp_pures.
    wp_load. wp_apply (wp_ReadBool with "[$]"). iIntros "* [% Hsl]". subst.
    wp_pures. by iApply "HΦ".
Qed.

(* relational rather than funtional *)
Definition read_int b0 v b err : Prop :=
  if decide (8 ≤ length b0) then
    v = le_to_u64 (take 8 b0) ∧
    b = drop 8 b0 ∧
    err = false
  else
    v = 0 ∧ b = [] ∧ err = true.

Lemma wp_ReadInt b0_sl dq (b0 : list w8) :
  {{{ own_slice_small b0_sl byteT dq b0 }}}
    ReadInt (slice_val b0_sl)
  {{{ sl v b err, RET (#v, slice_val sl, #err);
      ⌜ read_int b0 v b err ⌝ ∗
      own_slice_small sl byteT dq b }}}.
Proof.
  iIntros (?) "Hpre HΦ". wp_rec.
  wp_apply wp_ref_to; [val_ty|]. iIntros (?) "Hb_ptr".
  wp_pures. wp_load. wp_apply wp_slice_len.
  iDestruct (own_slice_small_sz with "[$]") as %Hsz.
  wp_pures. wp_if_destruct.
  - wp_pures. replace (slice.nil) with (slice_val Slice.nil) by done. iApply "HΦ".
    iDestruct (own_slice_small_nil) as "$".
    { done. }
    iPureIntro. unfold read_int. rewrite decide_False //. word.
  - wp_load.
    pose proof (take_drop 8 b0) as Hb.
    rewrite -[take _ _]le_to_u64_le in Hb.
    2:{ rewrite length_take. word. } rewrite -Hb.
    wp_apply (wp_ReadInt with "[$]").
    iIntros (?) "Hsl". wp_pures. iApply "HΦ". iFrame.
    iPureIntro. unfold read_int.
    rewrite -> le_to_u64_le by len.
    rewrite take_app take_take take_drop length_take.
    rewrite decide_True //.
    { split_and!; try done. f_equal.
      rewrite -> Nat.min_l by word. rewrite -> Nat.min_l by word.
      simpl. rewrite take_0 app_nil_r //.
    }
    word.
Qed.

End wps.
