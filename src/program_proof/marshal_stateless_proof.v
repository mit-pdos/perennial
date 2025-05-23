From Perennial.Helpers Require Import List.

From Goose.github_com.tchajed Require Import marshal.
From Perennial.goose_lang.lib Require Import encoding.

From Perennial.program_proof Require Import proof_prelude std_proof.
From Perennial.goose_lang.lib Require Import slice.pred_slice.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section goose_lang.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.

Implicit Types (v:val).

Definition uint64_has_encoding (encoded : list u8) (x : u64) : Prop :=
  encoded = u64_le x.

Definition uint32_has_encoding (encoded : list u8) (x : u32) : Prop :=
  encoded = u32_le x.

Definition bool_has_encoding (encoded : list u8) (x : bool) : Prop :=
  encoded = [if x then W8 1 else W8 0].

Definition string_has_encoding (encoded : list u8) (x : byte_string) : Prop :=
  encoded = x.

Definition byte_has_encoding (encoded : list u8) (x : list u8) : Prop :=
  encoded = x.

Theorem wp_ReadInt tail s q x :
  {{{ own_slice_small s byteT q (u64_le x ++ tail) }}}
    ReadInt (slice_val s)
  {{{ s', RET (#x, slice_val s'); own_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_rec.
  wp_apply (wp_UInt64Get_unchanged with "Hs").
  { rewrite /list.untype fmap_app take_app_length' //. len. }
  iIntros "Hs".
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'". wp_pures. iApply "HΦ".
  rewrite drop_app_length'; [done|len].
Qed.

Theorem wp_ReadInt32 tail s q (x: u32) :
  {{{ own_slice_small s byteT q (u32_le x ++ tail) }}}
    ReadInt32 (slice_val s)
  {{{ s', RET (#x, slice_val s'); own_slice_small s' byteT q tail }}}.
Proof.
  iIntros (Φ) "Hs HΦ". wp_rec.
  wp_apply (wp_UInt32Get_unchanged with "Hs").
  { rewrite /list.untype fmap_app take_app_length' //. len. }
  iIntros "Hs".
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'". wp_pures. iApply "HΦ".
  rewrite drop_app_length'; [done|len].
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

Lemma drop_succ :
  forall {A : Type} (l : list A) (x : A) (l' : list A) (n : nat),
  l !! n = Some x -> drop n l = x :: l' -> drop (S n) l = l'.
Proof.
  intros A l x l' n Helem Hd.
  pose proof drop_S l x n. apply H in Helem. rewrite Helem in Hd.
  inversion Hd. reflexivity.
Qed.

Fixpoint encodes {A:Type} (enc : list u8) (xs : list A)
  (has_encoding : list u8 -> A -> Prop): Prop :=
  match xs with
  | [] => enc = []
  | x :: xs' => exists bs bs', xs = x :: xs' /\
                         enc = bs ++ bs' /\
                         has_encoding bs x /\
                         encodes bs' xs' has_encoding
  end.

Local Lemma encodes_app {A:Type} (has_encoding : list u8 -> A -> Prop) :
  forall (xs : list A) (enc : list u8) (enc' : list u8) (x : A),
  encodes enc xs has_encoding /\
  has_encoding enc' x ->
  encodes (enc ++ enc') (xs ++ [x]) has_encoding.
Proof.
  intros xs.
  induction xs as [|x].
  - intros enc enc' x [Henc Hhe]. unfold encodes in Henc. rewrite Henc.
    simpl. exists enc', []. rewrite app_nil_r. split; done.
  - intros enc enc' x' [Henc Hhe].
    unfold encodes in Henc.
    destruct Henc as (enc__x & enc__xs & ? & Hbreak_enc & Hencx & Hbase_enc).
    fold (encodes enc__xs xs has_encoding) in Hbase_enc.
    rewrite Hbreak_enc.
    unfold encodes. simpl.
    exists enc__x, (enc__xs ++ enc').
    fold (encodes (enc__xs ++ enc') (xs ++ [x']) has_encoding).
    rewrite app_assoc.
    split; first reflexivity.
    split; first reflexivity.
    split; first exact.
    apply IHxs. exact.
Qed.  

Theorem wp_ReadSlice {X : Type} {goT : ty} (enc : list u8) (enc_sl : Slice.t)
  (xs : list X) (count : w64) (has_encoding : list u8 -> X -> Prop)
  (own : val -> X -> dfrac -> iProp Σ) (readOne : val) (suffix : list u8) (dq : dfrac) :
  (∀ (v : val) (x : X) (dq : dfrac), own v x dq -∗ ⌜val_ty v goT⌝) ->
  has_zero goT ->
  {{{
        "Hsl" ∷ own_slice_small enc_sl byteT dq (enc ++ suffix) ∗
        "%Henc" ∷ ⌜encodes enc xs has_encoding⌝ ∗
        "%Hcount" ∷ ⌜uint.nat count = length xs⌝ ∗
        "#HreadOne" ∷ ∀ enc' enc_sl' suffix' x,
          {{{
                own_slice_small enc_sl' byteT dq (enc' ++ suffix') ∗
                ⌜has_encoding enc' x⌝
          }}}
            readOne (slice_val enc_sl')
          {{{
                (v : val) (suff_sl : Slice.t), RET (v, slice_val suff_sl);
                own v x (DfracOwn 1) ∗
                own_slice_small suff_sl byteT dq suffix'
          }}}
  }}}
    ReadSlice goT (slice_val enc_sl) #count readOne
  {{{
        vals b2, RET (slice_val vals, slice_val b2);
        is_pred_slice own vals goT (DfracOwn 1) xs ∗
        own_slice_small b2 byteT dq suffix
  }}}.
Proof.
  iIntros (Hval_ty Hzero Φ) "Hpre HΦ". iNamed "Hpre".
  wp_rec. wp_pures.

  wp_apply (wp_ref_to); first val_ty. iIntros (l__b2) "Henc_sl".
  wp_pures.

  wp_apply (pred_slice.wp_NewSlice_0 own); first done.
  iIntros (gxs) "[Hgxs Hgxs_cap]".

  wp_apply (wp_ref_to); first val_ty. iIntros (l__xs) "Hxs_sl".
  wp_pures.

  wp_apply (wp_ref_to); first val_ty. iIntros (l__i) "Hi".
  wp_pures.

  wp_apply (wp_forUpto'
              (λ i, ∃ (enc' : list u8) (enc_sl' gxs' : Slice.t),
                   (* Loop Bounds *)
                   "%Hi_ge" ∷ ⌜0 ≤ uint.nat i⌝ ∗
                   "%Hi_le" ∷ ⌜uint.nat i <= length xs⌝ ∗
                   (* Encoding *)
                   "%H_b2_enc" ∷ ⌜encodes enc' (drop (uint.nat i) xs) has_encoding⌝ ∗
                   "H_b2_sl" ∷ own_slice_small enc_sl' byteT dq (enc' ++ suffix) ∗
                   (* Outside variables *)
                   "Henc_sl" ∷ l__b2 ↦[slice.T byteT] enc_sl' ∗
                   "Hxs_sl" ∷ l__xs ↦[slice.T goT] gxs' ∗
                   "Hxs" ∷ is_pred_slice own gxs' goT (DfracOwn 1) (take (uint.nat i) xs) ∗
                   "Hxs_cap" ∷ own_slice_cap gxs' goT
              )%I
              with "[$Hi $Hsl $Henc_sl $Hgxs $Hgxs_cap $Hxs_sl]"
           ).
  - iSplit; first word. 
    iPureIntro.
    split; first word. split; first word. done.
  - clear Φ. iIntros "!>" (i Φ) "[IH (i & %Hle)] HΦ". iNamed "IH".
    wp_pures. wp_load.
    assert ((uint.nat i <= length xs)%nat) as Hi_length. { word. }
    assert ((uint.nat i < length xs)%nat) as Hi_l_ne. { word. }
    apply drop_lt in Hi_l_ne.
    unfold encodes in H_b2_enc.
    destruct (drop (uint.nat i) xs) eqn:Hdrop. { contradiction. }
    destruct H_b2_enc as (H_b2_bs & H_b2_bs' & H_b2_enc &
                            H_b2_enc' & H_b2_encoding & H_b2_enc_next).
    rewrite H_b2_enc'. rewrite <- app_assoc.
    wp_apply ("HreadOne" with "[$H_b2_sl //]").
    iIntros (??) "(Hown_x & Hsuff_sl)".
    wp_pures. wp_load.
    pose proof (Hval_ty v x (DfracOwn 1)) as Hval.
    iDestruct (Hval with "Hown_x") as "%Hval_x".
    wp_apply (pred_slice.wp_SliceAppend with "[$Hxs $Hxs_cap $Hown_x]").
    { done. } { done. }
    iIntros (s') "Hs'".
    wp_store. wp_store.

    iModIntro. iApply "HΦ". iFrame.
    pose proof (take_drop (uint.nat i) xs) as H_td.
    rewrite Hdrop in H_td.
    pose proof (length_take_le xs $ uint.nat i) as H_tl.
    apply H_tl in Hi_length. symmetry in Hi_length.
    pose proof (list_lookup_middle (take (uint.nat i) xs) l x $ uint.nat i) as Hmiddle. 
    apply Hmiddle in Hi_length as Hlookup.
    apply take_S_r in Hlookup as Htake.
    rewrite H_td in Htake.
    rewrite <- Htake.
    replace (uint.nat (w64_word_instance.(word.add) i (W64 1)))
      with (S (uint.nat i)) by word.

    iFrame. iPureIntro.
    split; first word. split; first word.
    apply drop_succ in Hdrop.
    + rewrite Hdrop. done.
    + rewrite <- H_td. done.

  - iIntros "[Hloop Hi]". iNamed "Hloop".
    wp_pures. wp_load. wp_load. wp_pures.
    iModIntro. iApply "HΦ".
    rewrite take_ge; [ | word ].
    rewrite Hcount in H_b2_enc.
    rewrite drop_all in H_b2_enc.
    unfold encodes in H_b2_enc.
    rewrite H_b2_enc.
    rewrite app_nil_l.
    iFrame.
Qed.

Theorem wp_ReadSlice' {X : Type} {V : IntoVal X} {goT: ty}
  (enc : list u8) (enc_sl : Slice.t) (xs : list X) (count : w64) (ValRel: IntoValForType X goT)
  (has_encoding : list u8 -> X -> Prop) (own : val -> X -> dfrac -> iProp Σ) (readOne : val)
  (suffix : list u8) (dq : dfrac) :
  (forall (v : val) (x : X) (dq : dfrac), own v x dq -∗ ⌜v = to_val x⌝) ->
  {{{ "Hsl" ∷ own_slice_small enc_sl byteT dq (enc ++ suffix) ∗
      "%Henc" ∷ ⌜encodes enc xs has_encoding⌝ ∗
      "%Hcount" ∷ ⌜uint.nat count = length xs⌝ ∗
      "#HreadOne" ∷ ∀ enc' enc_sl' suffix' x,
      {{{ own_slice_small enc_sl' byteT dq (enc' ++ suffix') ∗
          ⌜has_encoding enc' x⌝
      }}}
        readOne (slice_val enc_sl')
      {{{ (v : val) (suff_sl : Slice.t), RET (v, slice_val suff_sl); own v x (DfracOwn 1) ∗
          own_slice_small suff_sl byteT dq suffix'
      }}}
  }}}
    ReadSlice goT (slice_val enc_sl) #count readOne
  {{{ vals b2, RET (slice_val vals, slice_val b2);
       own_slice vals goT (DfracOwn 1) xs ∗
       own_slice_small b2 byteT dq suffix
  }}}.
Proof.
  iIntros (Hown_val ϕ) "Hpre HΦ". iNamed "Hpre". wp_rec. wp_pures.
  wp_apply (wp_ref_to); first val_ty. iIntros (l__b2) "Henc_sl".
  wp_pures.

  wp_apply (wp_NewSlice). iIntros (gxs) "Hgxs".
  wp_apply (wp_ref_to); first val_ty. iIntros (l__xs) "Hxs_sl".
  wp_pures.

  wp_apply (wp_ref_to); first val_ty. iIntros (l__i) "Hi".
  wp_pures.

  wp_apply (wp_forUpto'
              (λ i, ∃ (enc' : list u8) (enc_sl' gxs' : Slice.t),
                   (* Loop Bounds *)
                   "%Hi_ge" ∷ ⌜0 ≤ uint.nat i⌝ ∗
                   "%Hi_le" ∷ ⌜uint.nat i <= length xs⌝ ∗
                   (* Encoding *)
                   "%H_b2_enc" ∷ ⌜encodes enc' (drop (uint.nat i) xs) has_encoding⌝ ∗
                   "H_b2_sl" ∷ own_slice_small enc_sl' byteT dq (enc' ++ suffix) ∗
                   (* Outside variables *)
                   "Henc_sl" ∷ l__b2 ↦[slice.T byteT] enc_sl' ∗
                   "Hxs_sl" ∷ l__xs ↦[slice.T goT] gxs' ∗
                   "Hxs" ∷ own_slice gxs' goT (DfracOwn 1) (take (uint.nat i) xs)
              )%I
              with "[$Hi $Hsl $Henc_sl $Hgxs $Hxs_sl]"
           ).
  - iSplit. { word. }
    iPureIntro.
    split; first word. split; first word. done.
  - clear ϕ. iIntros "!>" (i Φ) "[IH (i & %Hle)] HΦ". iNamed "IH".
    wp_pures. wp_load.
    assert ((uint.nat i <= length xs)%nat) as Hi_length. { word. }
    assert ((uint.nat i < length xs)%nat) as Hi_l_ne. { word. }
    apply drop_lt in Hi_l_ne.
    unfold encodes in H_b2_enc.
    destruct (drop (uint.nat i) xs) eqn:Hdrop. { contradiction. }
    destruct H_b2_enc as (H_b2_bs & H_b2_bs' & H_b2_enc & H_b2_enc' & H_b2_encoding & H_b2_enc_next).
    rewrite H_b2_enc'. rewrite <- app_assoc.
    wp_apply ("HreadOne" with "[$H_b2_sl //]").
    iIntros (??) "(Hown_x & Hsuff_sl)".
    wp_pures. wp_load.
    pose proof (Hown_val v x (DfracOwn 1)) as Hto_val.
    iApply Hto_val in "Hown_x". iDestruct "Hown_x" as "%Hown_x".
    rewrite Hown_x.
    wp_apply (wp_SliceAppend with "[$Hxs]"). iIntros (s') "Hs'".
    wp_store. wp_store.

    iModIntro. iApply "HΦ". iFrame.
    pose proof (take_drop (uint.nat i) xs) as H_td.
    rewrite Hdrop in H_td.
    pose proof (length_take_le xs $ uint.nat i) as H_tl.
    apply H_tl in Hi_length. symmetry in Hi_length.
    pose proof (list_lookup_middle (take (uint.nat i) xs) l x $ uint.nat i) as Hmiddle.
    apply Hmiddle in Hi_length as Hlookup.
    apply take_S_r in Hlookup as Htake.
    rewrite H_td in Htake.
    rewrite <- Htake.
    replace (uint.nat (w64_word_instance.(word.add) i (W64 1))) with (S (uint.nat i)) by word.
    iFrame. iPureIntro.
    split; first word. split; first word.
    apply drop_succ in Hdrop.
    + rewrite Hdrop. done.
    + rewrite <- H_td. done.
  - iIntros "[Hloop Hi]". iNamed "Hloop".
    wp_pures. wp_load. wp_load. wp_pures.
    iModIntro. iApply "HΦ".
    replace (uint.nat (W64 (length xs))) with (length xs) by word.
    replace (uint.nat (W64 (length xs))) with (length xs) in H_b2_enc by word.
    rewrite take_ge; [ | word ].
    rewrite drop_ge in H_b2_enc; [ | word ].
    unfold encodes in H_b2_enc. rewrite H_b2_enc. rewrite app_nil_l.
    iFrame.
Qed.

Theorem wp_ReadSliceLenPrefix {X : Type} {goT : ty} (enc : list u8) (enc_sl : Slice.t)
  (xs : list X) (count : w64) (has_encoding : list u8 -> X -> Prop)
  (own : val -> X -> dfrac -> iProp Σ) (readOne : val) (suffix : list u8) (dq : dfrac) :
  (∀ (v : val) (x : X) (dq : dfrac), own v x dq -∗ ⌜val_ty v goT⌝) ->
  has_zero goT ->
  {{{
        "Hsl" ∷ own_slice_small enc_sl byteT dq (u64_le count ++ enc ++ suffix) ∗
        "%Henc" ∷ ⌜encodes enc xs has_encoding⌝ ∗
        "%Hcount" ∷ ⌜uint.nat count = length xs⌝ ∗
        "#HreadOne" ∷ ∀ enc' enc_sl' suffix' x,
          {{{
                own_slice_small enc_sl' byteT dq (enc' ++ suffix') ∗
                ⌜has_encoding enc' x⌝
          }}}
            readOne (slice_val enc_sl')
          {{{
                (v : val) (suff_sl : Slice.t), RET (v, slice_val suff_sl);
                own v x (DfracOwn 1) ∗
                own_slice_small suff_sl byteT dq suffix'
          }}}
  }}}
    ReadSliceLenPrefix goT (slice_val enc_sl) readOne
  {{{
        vals b2, RET (slice_val vals, slice_val b2);
        is_pred_slice own vals goT (DfracOwn 1) xs ∗
        own_slice_small b2 byteT dq suffix
  }}}.
Proof.
  iIntros (Hval_ty Hzero Φ) "Hpre HΦ". iNamed "Hpre".
  wp_rec. wp_pures.

  wp_apply (wp_ReadInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures.

  wp_apply (wp_ReadSlice with "[Hsl]").
  { done. } { done. }
  {
    iFrame.
    iSplit; first done.
    iSplit; first done.
    done.
  }
  iApply "HΦ".
Qed.

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
  { len. }
  iIntros "Hsl". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_pures. iApply "HΦ". iModIntro.
  rewrite /own_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  { rewrite take_app_length' //. len. }
  rewrite drop_ge; [|len].
  by list_simplifier.
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
  { len. }
  iIntros "Hsl". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_pures. iApply "HΦ". iModIntro.
  rewrite /own_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  { rewrite take_app_length' //. len. }
  rewrite drop_ge; [|len].
  by list_simplifier.
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

Theorem wp_WriteSlice {X : Type} {goT : ty} (pre_sl : Slice.t) (xsl : Slice.t)
  (xs : list X) (has_encoding : list u8 -> X -> Prop) (own : val -> X -> dfrac -> iProp Σ)
  (writeOne : val) (prefix : list u8) (dq : dfrac) :
  {{{
        "Hsl" ∷ own_slice pre_sl byteT (DfracOwn 1) prefix ∗
        "Hown" ∷ is_pred_slice own xsl goT dq xs ∗
        "#HwriteOne" ∷ ∀ v pre_sl' (prefix' : list u8) x,
          {{{
                own v x dq ∗
                own_slice pre_sl' byteT (DfracOwn 1) prefix'
          }}}
            writeOne (slice_val pre_sl') v
          {{{
                (enc : list u8) (enc_sl : Slice.t), RET slice_val enc_sl;
                ⌜ has_encoding enc x ⌝ ∗
                own v x dq ∗
                own_slice enc_sl byteT (DfracOwn 1) (prefix' ++ enc)
          }}}
  }}}
    WriteSlice goT (slice_val pre_sl) (slice_val xsl) writeOne
  {{{
        enc enc_sl, RET slice_val enc_sl;
        is_pred_slice own xsl goT dq xs ∗
        ⌜ encodes enc xs has_encoding ⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ enc)
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iNamed "Hpre".
  wp_rec. wp_pures.

  wp_apply (wp_ref_to); first val_ty. iIntros (l__b2) "Hb2".
  wp_pures.

  iUnfold is_pred_slice in "Hown".
  iDestruct "Hown" as "[%vs [Hxsl Hown]]".
  iDestruct (own_slice_small_sz with "Hxsl") as "%Hxsz".
  iDestruct (big_sepL2_length with "Hown") as "%Hlen".

  wp_apply (pred_slice.wp_forSlice own
              (λ i, ∃ (enc' : list u8) (enc_sl' : Slice.t),
                  (* Encoding *)
                  "%H_b2_enc" ∷ ⌜ encodes enc' (take (uint.nat i) xs) has_encoding ⌝ ∗
                  "H_b2_sl" ∷ own_slice enc_sl' byteT (DfracOwn 1) (prefix ++ enc') ∗
                  (* Outside Variables *)
                  "Henc_sl" ∷ l__b2 ↦[slice.T byteT] enc_sl'
              )%I
             with "[] [Hxsl Hown Hsl $Hb2]").
  2:{ iUnfold is_pred_slice. iSplitL "Hsl".
      + iExists []. rewrite app_nil_r. iFrame. done.
      + iExists vs. iFrame. }
  {
    clear Φ.
    iIntros (??? Φ) "!> (HI0 & Hownx & %Hsz & %Hxsi) HΦ".
    iNamed "HI0". wp_pures.
    wp_load.
    wp_apply ("HwriteOne" with "[$Hownx $H_b2_sl]").
    iIntros (encx enc_slx) "(%Hencx & Hownx & Hsl)".
    rewrite <- app_assoc.
    wp_store.

    iModIntro. iApply "HΦ".
    iSplitR "Hownx".
    + iExists (enc' ++ encx), enc_slx. iFrame.
      iPureIntro. 
      replace (uint.nat (word.add i 1)) with (S (uint.nat i)) by word.
      assert (uint.nat i < length xs) as Hixs by word.
      pose proof (take_S_r xs (uint.nat i) x) as Htsr.
      apply Htsr in Hxsi as Htsrs.
      rewrite Htsrs.
      destruct (take (uint.nat i) xs) eqn:Htake.
      - unfold encodes in H_b2_enc.
        rewrite H_b2_enc.
        simpl. exists encx, [].
        repeat split.
        { rewrite app_nil_r. reflexivity. }
        done.
      - apply encodes_app. done.
    + iFrame.
  }
  iIntros "[Hloop Hsl]". iNamed "Hloop".
  wp_pures. wp_load. iModIntro.
  iApply "HΦ". iFrame.
  rewrite Hlen in Hxsz.
  rewrite <- Hxsz in H_b2_enc.
  rewrite firstn_all in H_b2_enc.
  done.
Qed.

Theorem wp_WriteSliceLenPrefix {X : Type} {goT : ty} (pre_sl : Slice.t) (xsl : Slice.t)
  (xs : list X) (has_encoding : list u8 -> X -> Prop) (own : val -> X -> dfrac -> iProp Σ)
  (writeOne : val) (prefix : list u8) (dq : dfrac) :
  {{{
        "Hsl" ∷ own_slice pre_sl byteT (DfracOwn 1) prefix ∗
        "Hown" ∷ is_pred_slice own xsl goT dq xs ∗
        "#HwriteOne" ∷ ∀ v pre_sl' (prefix' : list u8) x,
          {{{
                own v x dq ∗
                own_slice pre_sl' byteT (DfracOwn 1) prefix'
          }}}
            writeOne (slice_val pre_sl') v
          {{{
                (enc : list u8) (enc_sl : Slice.t), RET slice_val enc_sl;
                ⌜ has_encoding enc x ⌝ ∗
                own v x dq ∗
                own_slice enc_sl byteT (DfracOwn 1) (prefix' ++ enc)
          }}}
  }}}
    WriteSliceLenPrefix goT (slice_val pre_sl) (slice_val xsl) writeOne
  {{{
        enc enc_sl, RET slice_val enc_sl;
        is_pred_slice own xsl goT dq xs ∗
        ⌜ encodes enc xs has_encoding ⌝ ∗
        own_slice enc_sl byteT (DfracOwn 1) (prefix ++ (u64_le $ length xs) ++ enc)
  }}}.
Proof. 
  iIntros (Φ) "Hpre HΦ". iNamed "Hpre".
  wp_rec. wp_pures.

  wp_apply (wp_slice_len).
  wp_apply (wp_WriteInt with "[$Hsl]").
  iIntros (?) "Hsl". wp_pures.

  wp_apply (wp_WriteSlice with "[Hown Hsl]").
  {
    iFrame.
    iApply "HwriteOne".
  }
  iIntros (??) "(Hown & %Henc & Hsl)".
  wp_pures. iModIntro.
  iDestruct (pred_slice_sz with "Hown") as "%Hsz".
  iApply "HΦ".
  rewrite <- app_assoc.
  rewrite Hsz.
  rewrite w64_to_nat_id.
  iFrame.
  done.
Qed.
  
End goose_lang.
