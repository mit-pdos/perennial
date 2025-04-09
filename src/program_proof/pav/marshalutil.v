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

End wps.
