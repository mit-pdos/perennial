From Perennial.Helpers Require Import List ListLen.

(* TODO: might need pure theory from here *)
(* From Perennial.goose_lang.lib Require Import encoding. *)

From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang Require Import std.
From New.proof Require Import proof_prelude.
From New.generatedproof.github_com.tchajed Require Import marshal.

Section goose_lang.
Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!goGlobalsGS Σ}.

#[global] Program Instance : IsPkgInit marshal := ltac2:(build_pkg_init ()).

Theorem wp_ReadInt tail (s: slice.t) q x :
  {{{ is_pkg_init marshal ∗ own_slice s q (u64_le x ++ tail) }}}
    marshal @ "ReadInt" #s
  {{{ s', RET (#x, #s'); own_slice s' q tail }}}.
Proof.
  wp_start as "Hs". wp_auto.
  (*
  wp_apply (wp_UInt64Get_unchanged with "Hs").
  { rewrite /list.untype fmap_app take_app_length' //. len. }
  iIntros "Hs".
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'". wp_auto. iApply "HΦ".
  rewrite drop_app_length'; [done|len].
Qed.
*)
Admitted.

Theorem wp_ReadInt32 tail s q (x: u32) :
  {{{ is_pkg_init marshal ∗ own_slice s q (u32_le x ++ tail) }}}
    marshal@"ReadInt32" #s
  {{{ s', RET (#x, #s'); own_slice s' q tail }}}.
Proof.
  wp_start as "Hs". wp_auto.
(*
  wp_apply (wp_UInt32Get_unchanged with "Hs").
  { rewrite /list.untype fmap_app take_app_length' //. len. }
  iIntros "Hs".
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'". wp_auto. iApply "HΦ".
  rewrite drop_app_length'; [done|len].
Qed.
*)
Admitted.

Theorem wp_ReadBytes s q (len: u64) (head tail : list u8) :
  length head = uint.nat len →
  {{{ is_pkg_init marshal ∗ own_slice s q (head ++ tail) }}}
    marshal@"ReadBytes" #s #len
  {{{ b s', RET (#b, #s'); own_slice b q head ∗ own_slice s' q tail }}}.
Proof.
  iIntros (Hlen). wp_start as "Hs". wp_auto.
(*
  iDestruct (own_slice_len with "Hs") as %Hsz.
  autorewrite with len in Hsz.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  wp_apply (wp_SliceTake).
  { word. }
  wp_apply (wp_SliceSkip).
  { word. }
  wp_auto.
  iModIntro.
  iApply "HΦ".
  iDestruct (slice_small_split _ len with "Hs") as "[Hs1 Hs2]".
  { len. }
  iSplitL "Hs1".
  - rewrite take_app_length' //.
  - rewrite drop_app_length' //.
Qed.
*)
Admitted.

Theorem wp_ReadBytesCopy s q (len: u64) (head tail : list u8) :
  length head = uint.nat len →
  {{{ is_pkg_init marshal ∗ own_slice s q (head ++ tail) }}}
    marshal@"ReadBytesCopy" #s #len
  {{{ b s', RET (#b, #s'); own_slice b (DfracOwn 1) head ∗ own_slice s' q tail }}}.
Proof.
  iIntros (Hlen). wp_start as "Hs". wp_auto.
(*
  wp_apply wp_NewSlice. iIntros (b) "Hb".
  iDestruct (own_slice_len with "Hs") as %Hsz.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  rewrite length_app in Hsz.
  wp_apply wp_SliceTake.
  { word. }
  iDestruct (slice_small_split _ len with "Hs") as "[Hs Hsclose]".
  { rewrite length_app. word. }
  iDestruct (own_slice_acc with "Hb") as "[Hb Hbclose]".
  wp_apply (wp_SliceCopy_full with "[$Hs $Hb]").
  { iPureIntro. len. }
  iIntros (l) "(%Hl_val & Hs & Hb)".
  iDestruct (own_slice_combine with "Hs Hsclose") as "Hs".
  { word. }
  rewrite take_drop.
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs'".
  wp_auto. iApply "HΦ". iModIntro. iSplitR "Hs'".
  - iApply "Hbclose". rewrite take_app_length' //.
  - rewrite drop_app_length' //.
Qed.
*)
Admitted.

Theorem wp_ReadLenPrefixedBytes s q (len: u64) (head tail : list u8):
  length head = uint.nat len →
  {{{
        is_pkg_init marshal ∗
        own_slice s q ((u64_le len) ++ head ++ tail)
  }}}
    marshal @ "ReadLenPrefixedBytes" #s
  {{{
        b s', RET (#b, #s'); own_slice b q head ∗ own_slice s' q tail
  }}}.
Proof.
  iIntros (Hlen).
  wp_start as "Hs". wp_auto.
  wp_apply (wp_ReadInt with "[$Hs]").
  iIntros (?) "Hs". wp_auto.
  wp_apply (wp_ReadBytes with "[$]"); first trivial.
  iIntros (??) "[Hb Hs]". wp_auto.
  iApply "HΦ". iFrame.
Qed.

Theorem wp_ReadBool s q (bit: u8) (tail: list u8) :
  {{{ is_pkg_init marshal ∗ own_slice s q (bit :: tail) }}}
    marshal@"ReadBool" (#s)
  {{{ (b: bool) s', RET (#b, #s');
      ⌜b = bool_decide (uint.Z bit ≠ 0)⌝ ∗
      own_slice s' q tail }}}.
Proof.
  wp_start as "Hs". wp_auto.
(*
  wp_apply (wp_SliceGet with "[$Hs]"); [ auto | ].
  iIntros "Hs".
  wp_auto.
  wp_apply (wp_SliceSkip_small with "Hs").
  { len. }
  iIntros (s') "Hs".
  wp_auto. iModIntro.
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
*)
Admitted.

Lemma drop_succ :
  forall {A : Type} (l : list A) (x : A) (l' : list A) (n : nat),
  l !! n = Some x -> drop n l = x :: l' -> drop (S n) l = l'.
Proof.
  intros A l x l' n Helem Hd.
  pose proof drop_S l x n. apply H in Helem. rewrite Helem in Hd.
  inversion Hd. reflexivity.
Qed.

Fixpoint encodes {A:Type} (enc : list u8) (xs : list A) (has_encoding : list u8 -> A -> Prop): Prop :=
  match xs with
    | [] => enc = []
    | x :: xs' => exists bs bs', xs = x :: xs' /\ enc = bs ++ bs' /\ has_encoding bs x /\ encodes bs' xs' has_encoding
  end.

Theorem wp_ReadSlice {X : Type} `{!IntoVal X} {goT: go_type} `{!IntoValTyped X goT} {C: Type}
  (enc : list u8) (enc_sl : slice.t) (cs : list C) (count : w64)
  (has_encoding : list u8 -> C -> Prop) (own: X -> C -> dfrac -> iProp Σ) (readOne : func.t)
  (suffix : list u8) (dq : dfrac) :
  {{{ is_pkg_init marshal ∗
      "Hsl" ∷ own_slice enc_sl dq (enc ++ suffix) ∗
      "%Henc" ∷ ⌜encodes enc cs has_encoding⌝ ∗
      "%Hcount" ∷ ⌜uint.nat count = length cs⌝ ∗
      "#HreadOne" ∷ ∀ enc' enc_sl' suffix' x,
      {{{ own_slice enc_sl' dq (enc' ++ suffix') ∗
          ⌜has_encoding enc' x⌝
      }}}
        #readOne (#enc_sl')
      {{{ v suff_sl, RET (#v, #suff_sl);
          own v x (DfracOwn 1) ∗
          own_slice suff_sl dq suffix'
      }}}
  }}}
    marshal @ "ReadSlice" #goT #enc_sl #count #readOne
  {{{ vals xs b2, RET (#vals, #b2);
       own_slice vals (DfracOwn 1) xs ∗
       ([∗ list] x;s ∈ xs;cs, own x s (DfracOwn 1)) ∗
       own_slice b2 dq suffix
  }}}.
Proof.
  wp_start as "Hpre". iNamed "Hpre". wp_auto.
(*
  wp_apply (wp_ref_to); first val_ty. iIntros (l__b2) "Henc_sl".
  wp_auto.

  wp_apply (wp_NewSlice). iIntros (gxs) "Hgxs".
  wp_apply (wp_ref_to); first val_ty. iIntros (l__xs) "Hxs_sl".
  wp_auto.

  wp_apply (wp_ref_to); first val_ty. iIntros (l__i) "Hi".
  wp_auto.

  wp_apply (wp_forUpto'
              (λ i, ∃ (enc' : list u8) (enc_sl' gxs' : slice.t),
                   (* Loop Bounds *)
                   "%Hi_ge" ∷ ⌜0 ≤ uint.nat i⌝ ∗
                   "%Hi_le" ∷ ⌜uint.nat i <= length xs⌝ ∗
                   (* Encoding *)
                   "%H_b2_enc" ∷ ⌜encodes enc' (drop (uint.nat i) xs) has_encoding⌝ ∗
                   "H_b2_sl" ∷ own_slice enc_sl' dq (enc' ++ suffix) ∗
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
    wp_auto. wp_load.
    assert ((uint.nat i <= length xs)%nat) as Hi_length. { word. }
    assert ((uint.nat i < length xs)%nat) as Hi_l_ne. { word. }
    apply drop_lt in Hi_l_ne.
    unfold encodes in H_b2_enc.
    destruct (drop (uint.nat i) xs) eqn:Hdrop. { contradiction. }
    destruct H_b2_enc as (H_b2_bs & H_b2_bs' & H_b2_enc & H_b2_enc' & H_b2_encoding & H_b2_enc_next).
    rewrite H_b2_enc'. rewrite <- app_assoc.
    wp_apply ("HreadOne" with "[$H_b2_sl //]").
    iIntros (??) "(Hown_x & Hsuff_sl)".
    wp_auto. wp_load.
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
    wp_auto. wp_load. wp_load. wp_auto.
    iModIntro. iApply "HΦ".
    replace (uint.nat (W64 (length xs))) with (length xs) by word.
    replace (uint.nat (W64 (length xs))) with (length xs) in H_b2_enc by word.
    rewrite take_ge; [ | word ].
    rewrite drop_ge in H_b2_enc; [ | word ].
    unfold encodes in H_b2_enc. rewrite H_b2_enc. rewrite app_nil_l.
    iFrame.
Qed.
*)
Admitted.

Local Theorem wp_compute_new_cap (old_cap min_cap : u64) :
  {{{ is_pkg_init marshal }}}
    marshal@"compute_new_cap" #old_cap #min_cap
  {{{ (new_cap : u64), RET #new_cap; ⌜uint.Z min_cap ≤ uint.Z new_cap⌝ }}}.
Proof.
  wp_start as "_". wp_auto.
  case_bool_decide; wp_auto.
  - iApply "HΦ". word.
  - iApply "HΦ". word.
Qed.

Local Theorem wp_reserve s (extra : u64) (vs : list u8) :
  {{{ is_pkg_init marshal ∗ own_slice s (DfracOwn 1) vs ∗ own_slice_cap w8 s }}}
    marshal@"reserve" (#s) #extra
  {{{ s', RET #s';
      ⌜uint.Z extra ≤ uint.Z (slice.cap_f s') - uint.Z (slice.len_f s')⌝ ∗
      own_slice s' (DfracOwn 1) vs ∗ own_slice_cap w8 s' }}}.
Proof.
  wp_start as "[Hs Hcap]". wp_auto.
(*
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len.
  wp_apply wp_SumAssumeNoOverflow. iIntros (Hsum).
  wp_auto. wp_apply wp_slice_cap.
  wp_if_destruct.
  - (* we have to grow. *)
    wp_apply wp_slice_cap.
    wp_apply wp_compute_new_cap.
    iIntros (new_cap Hcap).
    wp_apply wp_slice_len.
    wp_apply wp_new_slice_cap; first done.
    { word. }
    iIntros (ptr) "Hnew". wp_auto.
    iDestruct (slice.own_slice_to_small with "Hs") as "Hs".
    iDestruct (slice.own_slice_acc with "Hnew") as "[Hnew Hcl]".
    wp_apply (slice.wp_SliceCopy_full with "[Hnew Hs]").
    { iFrame. iPureIntro. rewrite list_untype_length Hsz length_replicate //. }
    iIntros "[_ Hnew]". iDestruct ("Hcl" with "Hnew") as "Hnew".
    wp_auto. iApply "HΦ". iModIntro. iFrame. iPureIntro. simpl. word.
  - (* already big enough *)
    iApply "HΦ". iFrame. word.
Qed.
*)
Admitted.

Theorem wp_WriteInt s x (vs : list u8) :
  {{{ is_pkg_init marshal ∗ own_slice s (DfracOwn 1) vs ∗ own_slice_cap w8 s }}}
    marshal@"WriteInt" (#s) #x
  {{{ s', RET #s'; own_slice s' (DfracOwn 1) (vs ++ u64_le x) ∗ own_slice_cap w8 s' }}}.
Proof.
  wp_start as "[Hs Hcap]". wp_auto.
(*
  wp_apply (wp_reserve with "Hs"). clear s. iIntros (s) "[% Hs]". wp_auto.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len. wp_auto.
  wp_apply (wp_SliceTake_full_cap with "Hs").
  { word. }
  iIntros (ex) "[%Hex Hsl]".
  set (s' := slice_take _ _).
  wp_apply wp_SliceSkip.
  { rewrite /slice_take /=. word. }
  iDestruct (slice.own_slice_split_acc s.(slice.len_f) with "Hsl") as "[Hsl Hclose]".
  { len. }
  wp_apply (wp_UInt64Put with "Hsl").
  { len. }
  iIntros "Hsl". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_auto. iApply "HΦ". iModIntro.
  rewrite /own_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  { rewrite take_app_length' //. len. }
  rewrite drop_ge; [|len].
  by list_simplifier.
Qed.
*)
Admitted.

Theorem wp_WriteInt32 s x (vs : list u8) :
  {{{ is_pkg_init marshal ∗ own_slice s (DfracOwn 1) vs ∗ own_slice_cap w8 s }}}
    marshal@"WriteInt32" (#s) #x
  {{{ s', RET #s'; own_slice s' (DfracOwn 1) (vs ++ u32_le x) ∗ own_slice_cap w8 s' }}}.
Proof.
  wp_start as "[Hs Hcap]". wp_auto.
(*
  wp_apply (wp_reserve with "Hs"). clear s. iIntros (s) "[% Hs]". wp_auto.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  iDestruct (own_slice_sz with "Hs") as %Hsz.
  wp_apply wp_slice_len. wp_auto.
  wp_apply (wp_SliceTake_full_cap with "Hs").
  { word. }
  iIntros (ex) "[%Hex Hsl]".
  set (s' := slice_take _ _).
  wp_apply wp_SliceSkip.
  { rewrite /slice_take /=. word. }
  iDestruct (slice.own_slice_split_acc s.(slice.len_f) with "Hsl") as "[Hsl Hclose]".
  { len. }
  wp_apply (wp_UInt32Put with "Hsl").
  { len. }
  iIntros "Hsl". iDestruct ("Hclose" with "Hsl") as "Hsl".
  wp_auto. iApply "HΦ". iModIntro.
  rewrite /own_slice. iExactEq "Hsl". repeat f_equal.
  rewrite /list.untype fmap_app. f_equal.
  { rewrite take_app_length' //. len. }
  rewrite drop_ge; [|len].
  by list_simplifier.
Qed.
*)
Admitted.

Theorem wp_WriteBytes s (vs : list u8) data_sl q (data : list u8) :
  {{{ is_pkg_init marshal ∗ own_slice s (DfracOwn 1) vs ∗ own_slice data_sl q data ∗ own_slice_cap w8 s }}}
    marshal@"WriteBytes" (#s) (#data_sl)
  {{{ s', RET #s';
    own_slice s' (DfracOwn 1) (vs ++ data) ∗
    own_slice_cap w8 s' ∗
    own_slice data_sl q data
  }}}.
Proof.
  wp_start as "(Hs & Hcap & Hdata)". wp_auto.
(*
  wp_apply (wp_SliceAppendSlice with "[$Hs $Hdata]"); first done.
  iIntros (s') "[Hs' Hdata]".
  iApply ("HΦ" with "[$]").
Qed.
*)
Admitted.

Theorem wp_WriteLenPrefixedBytes s (vs : list u8) data_sl q (data : list u8) :
  {{{
        is_pkg_init marshal ∗
        own_slice s (DfracOwn 1) vs ∗
        own_slice data_sl q data ∗
        own_slice_cap w8 s
  }}}
    marshal @ "WriteLenPrefixedBytes" #s #data_sl
  {{{
        s', RET #s';
        own_slice s' (DfracOwn 1) (vs ++ (u64_le $ length data) ++ data) ∗
        own_slice_cap w8 s' ∗
        own_slice data_sl q data
  }}}.
Proof.
  wp_start as "(Hs & Hdata & Hscap)". wp_auto.
  wp_apply (wp_WriteInt with "[$Hs $Hscap]").
  iIntros (s') "[Hs' Hscap]". wp_auto.
  wp_apply (wp_WriteBytes with "[$Hs' $Hdata $Hscap]").
  iIntros (s'0) "(Hs & Hscap & Hdata)". wp_auto.
  iApply "HΦ".
  rewrite -app_assoc.
  iDestruct (own_slice_len with "Hdata") as "%Hdlen".
  rewrite Hdlen.
  rewrite w64_to_nat_id. 
  iFrame.
Qed.

Theorem wp_WriteBool s (vs: list u8) (b: bool) :
  {{{ is_pkg_init marshal ∗ own_slice s (DfracOwn 1) vs ∗ own_slice_cap w8 s }}}
    marshal@"WriteBool" #s #b
  {{{ s', RET (#s');
      own_slice s' (DfracOwn 1) (vs ++ [if b then W8 1 else W8 0]) ∗
      own_slice_cap w8 s'
   }}}.
Proof.
  wp_start as "[Hs Hcap]". wp_auto.
  destruct b; wp_auto.
(*
  - wp_apply (wp_SliceAppend with "Hs"); auto.
  - wp_apply (wp_SliceAppend with "Hs"); auto.
Qed.
*)
Admitted.

Theorem wp_WriteSlice {X : Type} `{!IntoVal X} {goT : go_type} `{!IntoValTyped X goT} {C: Type}
  (pre_sl : slice.t) (prefix : list u8) (xsl : slice.t) (xs : list X) (cs: list C)
  (has_encoding : list u8 -> C -> Prop) (own : X -> C -> dfrac -> iProp Σ) (writeOne : func.t) (dq : dfrac) :
  {{{   is_pkg_init marshal ∗
        "Hsl" ∷ own_slice pre_sl (DfracOwn 1) prefix ∗
        "Hcap" ∷ own_slice_cap w8 pre_sl ∗
        "Hown" ∷ own_slice xsl dq xs ∗
        "Hpred" ∷ ([∗ list] x;c ∈ xs;cs, own x c dq) ∗ 
        "#Hwriteone" ∷ ∀ pre_sl' (prefix' : list u8) x c,
          {{{
                own x c dq ∗
                own_slice pre_sl' (DfracOwn 1) prefix' ∗
                own_slice_cap w8 pre_sl'
          }}}
            #writeOne #pre_sl' #x
          {{{
                (enc : list u8) (enc_sl : slice.t), RET #enc_sl;
                ⌜ has_encoding enc c ⌝ ∗
                own x c dq ∗
                own_slice enc_sl (DfracOwn 1) (prefix' ++ enc) ∗
                own_slice_cap w8 enc_sl
          }}}
  }}}
    marshal @ "WriteSlice" #goT #pre_sl #xsl #writeOne
  {{{
        enc enc_sl, RET #enc_sl;
        own_slice xsl dq xs ∗
        ([∗ list] x;c ∈ xs;cs, own x c dq) ∗ 
        ⌜ encodes enc cs has_encoding ⌝ ∗
        own_slice enc_sl (DfracOwn 1) (prefix ++ enc) ∗
        own_slice_cap w8 enc_sl
  }}}.
Proof.
  wp_start as "Hpre". iNamed "Hpre". wp_auto.
(*
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
*)
Admitted.

End goose_lang.
