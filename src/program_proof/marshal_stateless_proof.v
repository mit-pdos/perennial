From Perennial.Helpers Require Import List.

From Goose.github_com.tchajed Require Import marshal.
From Perennial.goose_lang.lib Require Import encoding.

From Perennial.program_proof Require Import proof_prelude std_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section goose_lang.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.

Implicit Types (v:val).

Theorem wp_ReadInt s q x tail :
  {{{ own_slice_small s byteT q (u64_le x ++ tail) }}}
    ReadInt (slice_val s)
  {{{ s', RET (#x, slice_val s'); own_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_rec.
  wp_apply (wp_UInt64Get_unchanged with "Hs").
  { rewrite /list.untype fmap_app take_app_length' //. }
  iIntros "Hs".
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'". wp_pures. iApply "HΦ". done.
Qed.

Theorem wp_ReadInt32 s q (x: u32) tail :
  {{{ own_slice_small s byteT q (u32_le x ++ tail) }}}
    ReadInt32 (slice_val s)
  {{{ s', RET (#x, slice_val s'); own_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_rec.
  wp_apply (wp_UInt32Get_unchanged with "Hs").
  { rewrite /list.untype fmap_app take_app_length' //. }
  iIntros "Hs".
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'". wp_pures. iApply "HΦ". done.
Qed.

Theorem wp_ReadBytes s q (len: u64) (head tail : list u8) :
  length head = uint.nat len →
  {{{ own_slice_small s byteT q (head ++ tail) }}}
    ReadBytes (slice_val s) #len
  {{{ b s', RET (slice_val b, slice_val s'); own_slice_small b byteT q head ∗ own_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Hlen Φ) "Hs HΦ".
  wp_rec. wp_pures.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  autorewrite with len in Hsz.
  iDestruct (own_slice_small_wf with "Hs") as %Hwf.
  wp_apply (wp_SliceTake).
  { word. }
  wp_apply (wp_SliceSkip).
  { word. }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iDestruct (slice_small_split _ len with "Hs") as "[Hs1 Hs2]".
  { len. }
  iSplitL "Hs1".
  - rewrite take_app_length' //.
  - rewrite drop_app_length' //.
Qed.

Theorem wp_ReadBytesCopy s q (len: u64) (head tail : list u8) :
  length head = uint.nat len →
  {{{ own_slice_small s byteT q (head ++ tail) }}}
    ReadBytesCopy (slice_val s) #len
  {{{ b s', RET (slice_val b, slice_val s'); own_slice b byteT (DfracOwn 1) head ∗ own_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Hlen Φ) "Hs HΦ". wp_rec. wp_pures.
  wp_apply wp_NewSlice. iIntros (b) "Hb".
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iDestruct (own_slice_small_wf with "Hs") as %Hwf.
  rewrite length_app in Hsz.
  wp_apply wp_SliceTake.
  { word. }
  iDestruct (slice_small_split _ len with "Hs") as "[Hs Hsclose]".
  { rewrite length_app. word. }
  iDestruct (own_slice_small_acc with "Hb") as "[Hb Hbclose]".
  wp_apply (wp_SliceCopy_full with "[$Hs $Hb]").
  { iPureIntro. len. }
  iIntros (l) "(%Hl_val & Hs & Hb)".
  iDestruct (own_slice_combine with "Hs Hsclose") as "Hs".
  { word. }
  rewrite take_drop.
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'".
  wp_pures. iApply "HΦ". iModIntro. iSplitR "Hs'".
  - iApply "Hbclose". rewrite take_app_length' //.
  - rewrite drop_app_length' //.
Qed.

Theorem wp_ReadBool s q (bit: u8) (tail: list u8) :
  {{{ own_slice_small s byteT q (bit :: tail) }}}
    ReadBool (slice_val s)
  {{{ (b: bool) s', RET (#b, slice_val s');
      ⌜b = bool_decide (uint.Z bit ≠ 0)⌝ ∗
      own_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_rec. wp_pures.
  wp_apply (wp_SliceGet with "[$Hs]"); [ auto | ].
  iIntros "Hs".
  wp_pures.
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs".
  wp_pures. iModIntro.
  iApply "HΦ".
  iSplit.
  { iPureIntro. rewrite -bool_decide_not !bool_decide_decide.
    assert (#bit ≠ #(U8 0) ↔ uint.Z bit ≠ 0).
    { apply not_iff_compat.
      split.
    - inversion 1; subst; auto.
    - intros H.
      repeat (f_equal; try word).
    }
    destruct (decide _), (decide _); auto; tauto.
  }
  iApply "Hs".
Qed.

Fixpoint encodes {A:Type} (enc : list u8) (xs : list A) (has_encoding : list u8 -> A -> Prop): Prop :=
  match xs with
    | [] => enc = []
    | x :: xs' => exists bs bs', xs = x :: xs' /\ enc = bs ++ bs' /\ has_encoding bs x /\ encodes bs' xs' has_encoding
  end.

Theorem wp_ReadSlice {A:Type} {V: IntoVal A} {goT: ty}
  (enc : list u8) (enc_sl : Slice.t) (count : u64) (args: list A) (ValRel: IntoValForType A goT)
  (has_encoding : list u8 -> A -> Prop) (own : loc -> A -> dfrac -> iProp Σ) (readOne : val)
  (suffix : list u8) (dq : dfrac) :
  {{{ "Hsl" ∷ own_slice_small enc_sl byteT dq (enc ++ suffix) ∗
      "%Henc" ∷ ⌜encodes enc args has_encoding⌝ ∗
      "%Hcount" ∷ ⌜ uint.nat count <= length args ⌝ ∗
      "#HreadOne" ∷ ∀ enc' enc_sl' suffix' x,
      {{{ own_slice_small enc_sl' byteT dq (enc' ++ suffix') ∗
          ⌜has_encoding enc' x⌝
      }}}
        readOne (slice_val enc_sl')
      {{{ x (v : A) suff_sl, RET (#x, slice_val suff_sl); own x v (DfracOwn 1) ∗
          own_slice_small suff_sl byteT dq suffix' ∗
          (* While this is true, I don't know if it is strong enough *)
          ⌜v ∈ args⌝
      }}}
  }}}
    ReadSlice goT (slice_val enc_sl) #count readOne
  {{{ xs b2, RET (slice_val xs, slice_val b2);
       own_slice_small b2 byteT dq suffix ∗
       own_slice_small xs goT dq args
  }}}.
Proof.
  iIntros (ϕ) "Hpre HΦ". iNamed "Hpre". wp_rec. wp_pures.
  wp_apply (wp_ref_to); first val_ty. iIntros (l__b2) "Henc_sl".
  wp_pures.

  wp_apply (wp_NewSlice). iIntros (xs) "Hxs".
  wp_apply (wp_ref_to); first val_ty. iIntros (l__xs) "Hxs_sl".
  wp_pures.

  wp_apply (wp_ref_to); first val_ty. iIntros (l__i) "Hi".
  wp_pures.

  wp_apply (wp_forUpto'
              (λ i, ∃ (enc' : list u8) (enc_sl' : Slice.t),
                   (* Loop Bounds *)
                   "%Hi_ge" ∷ ⌜0 ≤ uint.nat i⌝ ∗
                   "%Hi_le" ∷ ⌜uint.nat i <= uint.Z count⌝ ∗
                   (* Encoding *)
                   "%H_b2_enc" ∷ ⌜encodes enc' (drop (uint.nat i) args) has_encoding⌝ ∗
                   "H_b2_sl" ∷ own_slice_small enc_sl' byteT dq (enc' ++ suffix) ∗
                   (* Outside variables *)
                   "Henc_sl" ∷ l__b2 ↦[slice.T byteT] enc_sl ∗
                   "Hxs" ∷ own_slice xs goT (DfracOwn 1) (take (uint.nat i) args) ∗
                   "Hxs_sl" ∷ l__xs ↦[slice.T goT] xs
              )%I
              with "[$Hi $Hsl $Henc_sl $Hxs $Hxs_sl]"
           ).
  - iSplit. { word. }
    iPureIntro.
    split; first word. split; first word. done.
  - clear ϕ. iIntros "!>" (i Φ) "[IH (i & %Hle)] HΦ". iNamed "IH".
    wp_pures. wp_load.
    assert (uint.nat i < length args) as Hi_length. { word. }
    unfold encodes in H_b2_enc.
    (* TODO Show that args can't be empty at this point to help reduce encodes *)
    pose proof (drop_lt args $ uint.nat i) as Hargs_ne.
    (* apply Hargs_ne in Hi_length. *)
    (* wp_apply ("HreadOne" with "[H_b2_sl]"). *)
    (* { iFrame. } *)
Admitted.

Local Theorem wp_compute_new_cap (old_cap min_cap : u64) :
  {{{ True }}}
    compute_new_cap #old_cap #min_cap
  {{{ (new_cap : u64), RET #new_cap; ⌜uint.Z min_cap ≤ uint.Z new_cap⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec. wp_pures.
  wp_apply wp_ref_to. { val_ty. }
  iIntros (l) "Hl". wp_pures.
  wp_load.
  wp_if_destruct.
  - wp_store. wp_load. iApply "HΦ". iPureIntro. done.
  - wp_load. iApply "HΦ". iPureIntro. move: Heqb. word.
Qed.

Local Theorem wp_reserve s (extra : u64) (vs : list u8) :
  {{{ own_slice s byteT (DfracOwn 1) vs }}}
    reserve (slice_val s) #extra
  {{{ s', RET slice_val s'; ⌜uint.Z extra ≤ Slice.extra s'⌝ ∗ own_slice s' byteT (DfracOwn 1) vs }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_rec.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len.
  wp_apply wp_SumAssumeNoOverflow. iIntros (Hsum).
  wp_pures. wp_apply wp_slice_cap.
  wp_if_destruct.
  - (* we have to grow. *)
    wp_apply wp_slice_cap.
    wp_apply wp_compute_new_cap.
    iIntros (new_cap Hcap).
    wp_apply wp_slice_len.
    wp_apply wp_new_slice_cap; first done.
    { word. }
    iIntros (ptr) "Hnew". wp_pures.
    iDestruct (slice.own_slice_to_small with "Hs") as "Hs".
    iDestruct (slice.own_slice_small_acc with "Hnew") as "[Hnew Hcl]".
    wp_apply (slice.wp_SliceCopy_full with "[Hnew Hs]").
    { iFrame. iPureIntro. rewrite list_untype_length Hsz length_replicate //. }
    iIntros "[_ Hnew]". iDestruct ("Hcl" with "Hnew") as "Hnew".
    wp_pures. iApply "HΦ". iModIntro. iFrame. iPureIntro. simpl. word.
  - (* already big enough *)
    iApply "HΦ". iFrame. word.
Qed.

Theorem wp_WriteInt s x (vs : list u8) :
  {{{ own_slice s byteT (DfracOwn 1) vs }}}
    WriteInt (slice_val s) #x
  {{{ s', RET slice_val s'; own_slice s' byteT (DfracOwn 1) (vs ++ u64_le x) }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_rec. wp_pures.
  wp_apply (wp_reserve with "Hs"). clear s. iIntros (s) "[% Hs]". wp_pures.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len. wp_pures.
  wp_apply (wp_SliceTake_full_cap with "Hs").
  { word. }
  iIntros (ex) "[%Hex Hsl]".
  set (s' := slice_take _ _).
  wp_apply wp_SliceSkip.
  { rewrite /slice_take /=. word. }
  iDestruct (slice.own_slice_split_acc s.(Slice.sz) with "Hsl") as "[Hsl Hclose]".
  { len. }
  wp_apply (wp_UInt64Put with "Hsl").
  { len. rewrite Hex. word. }
  iIntros "Hsl". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_pures. iApply "HΦ". iModIntro.
  rewrite /own_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  { rewrite take_app_length' //. len. }
  rewrite drop_ge //. len. rewrite Hex. word.
Qed.

Theorem wp_WriteInt32 s x (vs : list u8) :
  {{{ own_slice s byteT (DfracOwn 1) vs }}}
    WriteInt32 (slice_val s) #x
  {{{ s', RET slice_val s'; own_slice s' byteT (DfracOwn 1) (vs ++ u32_le x) }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_rec. wp_pures.
  wp_apply (wp_reserve with "Hs"). clear s. iIntros (s) "[% Hs]". wp_pures.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len. wp_pures.
  wp_apply (wp_SliceTake_full_cap with "Hs").
  { word. }
  iIntros (ex) "[%Hex Hsl]".
  set (s' := slice_take _ _).
  wp_apply wp_SliceSkip.
  { rewrite /slice_take /=. word. }
  iDestruct (slice.own_slice_split_acc s.(Slice.sz) with "Hsl") as "[Hsl Hclose]".
  { len. }
  wp_apply (wp_UInt32Put with "Hsl").
  { len. rewrite Hex. word. }
  iIntros "Hsl". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_pures. iApply "HΦ". iModIntro.
  rewrite /own_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  { rewrite take_app_length' //. len. }
  rewrite drop_ge //. len. rewrite Hex. word.
Qed.

Theorem wp_WriteBytes s (vs : list u8) data_sl q (data : list u8) :
  {{{ own_slice s byteT (DfracOwn 1) vs ∗ own_slice_small data_sl byteT q data }}}
    WriteBytes (slice_val s) (slice_val data_sl)
  {{{ s', RET slice_val s';
    own_slice s' byteT (DfracOwn 1) (vs ++ data) ∗
    own_slice_small data_sl byteT q data
  }}}.
Proof.
  iIntros (Φ) "[Hs Hdata] HΦ". wp_rec. wp_pures.
  wp_apply (wp_SliceAppendSlice with "[$Hs $Hdata]"); first done.
  iIntros (s') "[Hs' Hdata]".
  iApply ("HΦ" with "[$]").
Qed.

Theorem wp_WriteBool s (vs: list u8) (b: bool) :
  {{{ own_slice s byteT (DfracOwn 1) vs }}}
    WriteBool (slice_val s) #b
  {{{ s', RET (slice_val s');
      own_slice s' byteT (DfracOwn 1) (vs ++ [if b then W8 1 else W8 0]) }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_rec. wp_pures.
  destruct b; wp_pures.
  - wp_apply (wp_SliceAppend with "Hs"); auto.
  - wp_apply (wp_SliceAppend with "Hs"); auto.
Qed.

End goose_lang.
