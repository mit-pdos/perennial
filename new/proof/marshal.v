From Perennial.Helpers Require Import List.

From New.code.github_com.tchajed Require Import marshal.
From Perennial.goose_lang.lib Require Import encoding.

From New.proof Require Import proof_prelude.

Notation encoded_length r := (length r) (only parsing).
Notation encode r := (r) (only parsing).

#[local] Open Scope Z.

Definition has_encoding (data: list u8) (r: list u8) :=
  r `prefix_of` data.

Typeclasses Opaque has_encoding.

Lemma has_encoding_length {data r} :
  has_encoding data r →
  (length r ≤ length data)%nat.
Proof.
  rewrite /has_encoding.
  intros H%prefix_length => //.
Qed.

Lemma has_encoding_app_characterization data r :
  has_encoding data r ↔
  ∃ extra, data = encode r ++ extra.
Proof.
  rewrite /has_encoding /prefix //.
Qed.

Section goose_lang.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.

Implicit Types (v:val).

Definition is_enc (enc_v:val) (sz:Z) (r: list val) (remaining: Z) : iProp Σ :=
  ∃ (s: slice.t) (off_l: loc) (data: list val),
    let off := Z.of_nat (length r) in
    "->" ∷ ⌜enc_v = struct.val Enc [("b" ::= slice.val s)%V; ("off" ::= #off_l)%V]⌝ ∗
    "Hs" ∷ own_slice s byteT (DfracOwn 1) data ∗
    "Hs_cap" ∷ own_slice_cap s byteT ∗
    "%Hsz" ∷ ⌜length data = Z.to_nat sz⌝ ∗
    "%Hremaining" ∷ ⌜(off + remaining)%Z = sz⌝ ∗
    "enc_off" ∷ off_l ↦[uint64T] #off ∗
    "%Hoff" ∷ ⌜0 ≤ off ≤ Z.of_nat (length data)⌝ ∗
    "%Hencoded" ∷ ⌜r `prefix_of` data⌝
.

Theorem wp_new_enc_from_slice stk E s (data: list val) :
  {{{ own_slice s byteT (DfracOwn 1) data ∗ own_slice_cap s byteT }}}
    NewEncFromSlice (slice.val s) @ stk; E
  {{{ (enc_v:val), RET enc_v; is_enc enc_v (length data) [] (length data) }}}.
Proof.
  iIntros (Φ) "[Hs Hcap] HΦ".
  wp_call.
  wp_alloc s_l as "s".
  wp_pures.
  wp_alloc off_l as "off".
  wp_load.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iExists _, _, _; rewrite /named; iFrame.
  rewrite nil_length.
  iSplit; first by eauto.
  iSplit.
  { iPureIntro.
    lia. }
  iSplit.
  { iPureIntro. lia. }
  iSplitL "off".
  { rewrite zero_val_unseal //=. }
  iPureIntro.
  split; first lia.
  apply prefix_nil.
Qed.

Theorem wp_new_enc stk E (sz: u64) :
  {{{ True }}}
    NewEnc #sz @ stk; E
  {{{ (enc_v:val), RET enc_v; is_enc enc_v (uint.Z sz) [] (uint.Z sz) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_alloc sz_l as "sz"; wp_pures.
  wp_alloc b_l as "b"; wp_pures.
  rewrite zero_val_unseal //=.
  wp_load.
  wp_apply wp_slice_make2; iIntros (s) "[Hs Hcap]"; wp_pures.
  wp_store; wp_pures.
  wp_load.
  wp_apply (wp_new_enc_from_slice with "[$Hs $Hcap]").
  iIntros (v) "Henc"; wp_pures.
  rewrite replicate_length.
  iModIntro.
  iApply "HΦ".
  iExactEq "Henc".
  f_equal; word.
Qed.

(* TODO: I thought there was already a way to do this *)
Lemma decide_reflect `{!Decision P} :
  (if decide P then True else False) → P.
Proof.
  destruct (decide P); intuition auto.
Qed.
Ltac decide_reflect :=
  apply decide_reflect;
  first [ vm_compute; exact I | fail "goal is false" ].

Theorem wp_Enc__PutInt stk E enc_v sz r (x:u64) remaining :
  8 ≤ remaining →
  {{{ is_enc enc_v sz r remaining }}}
    Enc__PutInt enc_v #x @ stk; E
  {{{ RET #(); is_enc enc_v sz (r ++ u64_le_bytes x) (remaining - 8) }}}.
Proof.
  iIntros (Hspace Φ) "Hpre HΦ"; iNamed "Hpre".
  set (off:=length r) in *.
  wp_call; wp_pures.
  wp_alloc enc_l as "enc"; wp_pures.
  wp_alloc x_l as "x".
  wp_pures.
  wp_alloc off_l' as "off"; wp_pures.
  iApply struct_fields_split in "enc"; eauto.
  { constructor. compute.
    decide_reflect. }
  rewrite /struct_fields struct.val_unseal /struct.val_def /= /append.
  iNamed "enc".
  repeat (wp_load || wp_pures || wp_store).

  (* TODO: finish porting this proof *)

  (*
  wp_apply wp_SliceSkip.
  { word. }
  iDestruct (own_slice_small_take_drop _ _ _ (W64 off) with "Hs") as "[Hs2 Hs1]".
  { word. }
  replace (uint.nat (W64 off)) with off by word.
  wp_apply (wp_UInt64Put with "Hs2").
  { len. }
  iIntros "Hs2".
  iDestruct (slice.own_slice_combine with "Hs1 Hs2") as "Hs"; first len.
  wp_pures.
  wp_load; wp_store.
  rewrite -fmap_drop drop_drop.
  iApply "HΦ".
  iExists _, _, _; iFrame.
  change (u64_le_bytes x) with (into_val.to_val (V:=u8) <$> u64_le x).
  rewrite -!fmap_app.
  iSplitR; first eauto.
  iFrame "Hs". iModIntro.
  rewrite encoded_length_app1.
  change (length (encode1 (EncUInt64 x))) with 8%nat.
  iSplitR; first by iPureIntro; len.
  iSplitR; first by iPureIntro; len.
  iSplitL "Hoff".
  { iExactEq "Hoff".
    rewrite /named.
    repeat (f_equal; try word). }
  iPureIntro; split.
  - len.
  - subst off.
    apply has_encoding_app; auto.
    eapply has_encoding_from_app; eauto.
*)
Admitted.

(* TODO: finish porting the file *)

(*
Theorem wp_Enc__PutInt32 stk E enc_v sz r (x:u32) remaining :
  4 ≤ remaining →
  {{{ is_enc enc_v sz r remaining }}}
    Enc__PutInt32 enc_v #x @ stk; E
  {{{ RET #(); is_enc enc_v sz (r ++ [EncUInt32 x]) (remaining - 4) }}}.
Proof.
  iIntros (Hspace Φ) "Hpre HΦ"; iNamed "Hpre".
  set (off:=encoded_length r) in *.
  wp_call.
  wp_load.
  wp_pures.
  iDestruct (own_slice_small_sz with "Hs") as %Hslice_len.
  wp_apply wp_SliceSkip.
  { word. }
  iDestruct (own_slice_small_take_drop _ _ _ (W64 off) with "Hs") as "[Hs2 Hs1]".
  { word. }
  replace (uint.nat (W64 off)) with off by word.
  wp_apply (wp_UInt32Put with "Hs2").
  { len. }
  iIntros "Hs2".
  iDestruct (slice.own_slice_combine with "Hs1 Hs2") as "Hs"; first len.
  wp_pures.
  wp_load; wp_store.
  rewrite -fmap_drop drop_drop.
  iApply "HΦ".
  iExists _, _, _; iFrame.
  change (u32_le_bytes x) with (into_val.to_val <$> u32_le x).
  rewrite -!fmap_app.
  iSplitR; first eauto.
  iFrame "Hs". iModIntro.
  rewrite encoded_length_app1.
  change (length (encode1 _)) with 4%nat.
  iSplitR; first by iPureIntro; len.
  iSplitR; first by iPureIntro; len.
  iSplitL "Hoff".
  { iExactEq "Hoff".
    rewrite /named.
    repeat (f_equal; try word). }
  iPureIntro; split.
  - len.
  - subst off.
    apply has_encoding_app; auto.
    eapply has_encoding_from_app; eauto.
Qed.

Local Lemma wp_bool2byte stk E (x:bool) :
  {{{ True }}}
    bool2byte #x @ stk; E
  {{{ RET #(W8 (if x then 1 else 0))%Z; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  destruct x; wp_pures; by iApply "HΦ".
Qed.

Theorem wp_Enc__PutBool stk E enc_v sz r (x:bool) remaining :
  1 ≤ remaining →
  {{{ is_enc enc_v sz r remaining }}}
    Enc__PutBool enc_v #x @ stk; E
  {{{ RET #(); is_enc enc_v sz (r ++ [EncBool x]) (remaining - 1) }}}.
Proof.
  iIntros (Hspace Φ) "Hpre HΦ"; iNamed "Hpre".
  set (off:=encoded_length r) in *.
  wp_call.
  wp_load.
  wp_pures.
  iDestruct (own_slice_small_sz with "Hs") as %Hslice_len.
  wp_pures.
  wp_apply wp_bool2byte.
  set (u:=W8 (if x then 1 else 0)%Z).
  wp_pures.
  wp_apply (wp_SliceSet (V:=byte) with "[$Hs]").
  { iPureIntro. apply lookup_lt_is_Some_2. word. }
  iIntros "Hs".
  wp_pures.
  wp_load. wp_store.
  iApply "HΦ". iModIntro.
  iExists _, _, _. iFrame.
  iSplit; eauto.
  rewrite insert_length.
  iSplit; eauto.
  rewrite encoded_length_app1. simpl.
  iSplit.
  { iPureIntro. word. }
  iSplit.
  { iExactEq "Hoff". rewrite /named. do 3 f_equal. word. }
  iPureIntro.
  split; first word.
  replace (<[uint.nat off:=u]> data) with
      (take off data ++ [u] ++ drop (off + 1) data); last first.
  { rewrite insert_take_drop. 2:word.
    repeat f_equal; word. }
  apply has_encoding_app; eauto.
  eapply has_encoding_from_app; eauto.
Qed.

Theorem wp_Enc__PutInts stk E enc_v sz r (x_s: Slice.t) q (xs:list u64) remaining :
  8*(Z.of_nat $ length xs) ≤ remaining →
  {{{ is_enc enc_v sz r remaining ∗ own_slice_small x_s uint64T q xs }}}
    Enc__PutInts enc_v (slice_val x_s) @ stk; E
  {{{ RET #(); is_enc enc_v sz (r ++ (EncUInt64 <$> xs)) (remaining - 8*(Z.of_nat $ length xs)) ∗
               own_slice_small x_s uint64T q xs }}}.
Proof.
  iIntros (Hbound Φ) "[Henc Hxs] HΦ".
  wp_rec; wp_pures.
  wp_apply (wp_forSlicePrefix
              (λ done todo,
                "Henc" ∷ is_enc enc_v sz
                        (r ++ (EncUInt64 <$> done))
                        (remaining - 8*(Z.of_nat $ length done)))%I
           with "[] [$Hxs Henc]").
  - clear Φ.
    iIntros (???? Hdonetodo) "!>".
    iIntros (Φ) "HI HΦ"; iNamed "HI".
    wp_pures.
    wp_apply (wp_Enc__PutInt with "Henc").
    { apply (f_equal length) in Hdonetodo; move: Hdonetodo; len. }
    iIntros "Henc".
    iApply "HΦ".
    iExactEq "Henc".
    rewrite /named; f_equal; len.
    rewrite fmap_app.
    rewrite -!app_assoc.
    reflexivity.
  - iExactEq "Henc".
    rewrite /named; f_equal; len.
    rewrite app_nil_r //.
  - iIntros "(Hs&HI)"; iNamed "HI".
    wp_pures. iApply "HΦ"; by iFrame.
Qed.

Hint Rewrite encoded_length_app1 : len.

Theorem wp_Enc__PutBytes stk E enc_v r sz remaining b_s q bs :
  Z.of_nat (length bs) ≤ remaining →
  {{{ is_enc enc_v sz r remaining ∗ own_slice_small b_s byteT q bs }}}
    Enc__PutBytes enc_v (slice_val b_s) @ stk; E
  {{{ RET #(); is_enc enc_v sz (r ++ [EncBytes bs]) (remaining - Z.of_nat (length bs)) ∗
               own_slice_small b_s byteT q bs }}}.
Proof.
  iIntros (Hbound Φ) "[Henc Hbs] HΦ"; iNamed "Henc".
  wp_call.
  wp_load; wp_pures.
  iDestruct (own_slice_small_sz with "Hs") as %Hs_sz.
  wp_apply wp_SliceSkip.
  { len. }
  iDestruct (slice_small_split _ (W64 (encoded_length r)) with "Hs") as "[Hs1 Hs2]"; first by len.
  wp_apply (wp_SliceCopy (V:=byte) with "[$Hbs $Hs2]"); first by len.
  iIntros "[Hbs Hs2]".
  iDestruct (own_slice_combine with "Hs1 Hs2") as "Hs"; first by len.
  wp_pures.
  wp_load; wp_store.
  iApply "HΦ".
  iFrame. iModIntro.
  iExists _; iSplitR; first by eauto.
  iSplitR.
  { iPureIntro; len. }
  iSplitR.
  { iPureIntro; len. simpl; len. }
  iSplitL "Hoff".
  { iExactEq "Hoff".
    rewrite /named.
    f_equal.
    f_equal.
    f_equal.
    len.
    simpl.
    word.
  }
  iPureIntro.
  split_and.
  - len.
    simpl; len.
  - replace (uint.nat (W64 (encoded_length r))) with (encoded_length r) by word.
    rewrite Hencoded.
    rewrite app_assoc.
    eapply has_encoding_from_app.
    rewrite encode_app encode_singleton //=.
Qed.

Theorem wp_Enc__Finish stk E enc_v r sz remaining :
  {{{ is_enc enc_v sz r remaining }}}
    Enc__Finish enc_v @ stk; E
  {{{ s data, RET slice_val s; ⌜has_encoding data r⌝ ∗
                               ⌜length data = Z.to_nat sz⌝ ∗
                               own_slice s byteT (DfracOwn 1) data }}}.
Proof.
  iIntros (Φ) "Henc HΦ"; iNamed "Henc"; subst.
  wp_call.
  iApply "HΦ"; by iFrame "∗ %".
Qed.

Definition is_dec (dec_v:val) (r:Rec) (s:Slice.t) (q:dfrac) (data: list u8): iProp Σ :=
  ∃ (off_l:loc) (off: u64),
    "->" ∷ ⌜dec_v = (slice_val s, (#off_l, #()))%V⌝ ∗
    "Hoff" ∷ off_l ↦[uint64T] #off ∗
    "%Hoff" ∷ ⌜uint.nat off ≤ length data⌝ ∗
    "Hs" ∷ own_slice_small s byteT q data ∗
    "%Henc" ∷ ⌜has_encoding (drop (uint.nat off) data) r⌝.

Lemma is_dec_to_own_slice_small dec_v r s q data :
  is_dec dec_v r s q data -∗
  own_slice_small s byteT q data.
Proof.
  iIntros "H". iNamed "H". iFrame.
Qed.

Theorem wp_new_dec stk E s q data r :
  has_encoding data r →
  {{{ own_slice_small s byteT q data }}}
    NewDec (slice_val s) @ stk; E
  {{{ dec_v, RET dec_v; is_dec dec_v r s q data }}}.
Proof.
  iIntros (Henc Φ) "Hs HΦ".
  wp_call.
  wp_apply (typed_mem.wp_AllocAt uint64T); eauto.
  iIntros (off_l) "Hoff".
  wp_pures.
  iApply "HΦ".
  iExists _, _; iFrame.
  iPureIntro.
  split_and!; auto; len.
Qed.

Hint Rewrite encoded_length_singleton : len.

Lemma encoded_length_cons x r :
  encoded_length (x::r) = (length (encode1 x) + encoded_length r)%nat.
Proof. rewrite encode_cons; len. Qed.

Theorem wp_Dec__GetInt stk E dec_v (x: u64) r s q data :
  {{{ is_dec dec_v (EncUInt64 x :: r) s q data }}}
    Dec__GetInt dec_v @ stk; E
  {{{ RET #x; is_dec dec_v r s q data }}}.
Proof.
  iIntros (Φ) "Hdec HΦ"; iNamed "Hdec".
  wp_call.
  wp_load; wp_pures.
  wp_load; wp_store.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  wp_apply wp_SliceSkip.
  { word. }
  iDestruct (slice.slice_small_split _ off with "Hs") as "[Hs1 Hs2]".
  { len. }
  wp_apply (wp_UInt64Get_unchanged with "Hs2").
  { eapply has_encoding_inv in Henc as [extra [Henc ?]].
    rewrite -fmap_drop -fmap_take.
    rewrite Henc.
    reflexivity. }
  iIntros "Hs2".
  iDestruct (slice.own_slice_small_take_drop_1 with "[$Hs1 $Hs2]") as "Hs"; first by word.
  iApply "HΦ".
  iExists _, _; iFrame.
  iSplitR; first by auto.
  pose proof (has_encoding_length Henc).
  autorewrite with len in H.
  rewrite encoded_length_cons in H.
  change (length (encode1 _)) with 8%nat in H.
  iSplitR; first iPureIntro.
  { word. }
  iPureIntro.
  replace (uint.nat (word.add off 8)) with (uint.nat off + 8)%nat by word.
  rewrite -drop_drop.
  apply has_encoding_inv in Henc as [extra [Henc ?]].
  rewrite Henc.
  rewrite encode_cons.
  eapply has_encoding_from_app.
  rewrite -app_assoc.
  rewrite drop_app_ge //.
Qed.

Theorem wp_Dec__GetInt32 stk E dec_v (x: u32) r s q data :
  {{{ is_dec dec_v (EncUInt32 x :: r) s q data }}}
    Dec__GetInt32 dec_v @ stk; E
  {{{ RET #x; is_dec dec_v r s q data }}}.
Proof.
  iIntros (Φ) "Hdec HΦ"; iNamed "Hdec".
  wp_call.
  wp_load; wp_pures.
  wp_load; wp_store.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  wp_apply wp_SliceSkip.
  { word. }
  iDestruct (slice.slice_small_split _ off with "Hs") as "[Hs1 Hs2]".
  { len. }
  wp_apply (wp_UInt32Get_unchanged with "Hs2").
  { eapply has_encoding_inv in Henc as [extra [Henc ?]].
    rewrite -fmap_drop -fmap_take.
    rewrite Henc.
    reflexivity. }
  iIntros "Hs2".
  iDestruct (slice.own_slice_small_take_drop_1 with "[$Hs1 $Hs2]") as "Hs"; first by word.
  iApply "HΦ".
  iExists _, _; iFrame.
  iSplitR; first by auto.
  pose proof (has_encoding_length Henc).
  autorewrite with len in H.
  rewrite encoded_length_cons in H.
  change (length (encode1 _)) with 4%nat in H.
  iSplitR; first iPureIntro.
  { word. }
  iPureIntro.
  replace (uint.nat (word.add off 4)) with (uint.nat off + 4)%nat by word.
  rewrite -drop_drop.
  apply has_encoding_inv in Henc as [extra [Henc ?]].
  rewrite Henc.
  rewrite encode_cons.
  eapply has_encoding_from_app.
  rewrite -app_assoc.
  rewrite drop_app_ge //.
Qed.

Theorem wp_Dec__GetBool stk E dec_v (x: bool) r s q data :
  {{{ is_dec dec_v (EncBool x :: r) s q data }}}
    Dec__GetBool dec_v @ stk; E
  {{{ RET #x; is_dec dec_v r s q data }}}.
Proof.
  iIntros (Φ) "Hdec HΦ"; iNamed "Hdec".
  wp_call.
  wp_load; wp_pures.
  wp_load; wp_store.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  pose proof (has_encoding_length Henc).
  autorewrite with len in H.
  rewrite encoded_length_cons in H.
  change (length (encode1 _)) with 1%nat in H.
  apply has_encoding_inv in Henc as [extra [Henc ?]].
  rewrite encode_cons in Henc.
  assert (drop (uint.nat off) data !! 0%nat = Some $ W8 (if x then 1 else 0)) as Hx.
  { rewrite Henc. done. }
  rewrite lookup_drop Nat.add_0_r in Hx.
  wp_apply (wp_SliceGet (V:=byte) with "[$Hs]").
  { done. }
  iIntros "Hl". wp_pures.
  destruct x; wp_pures; iApply "HΦ";
    iExists _, _; iFrame; iPureIntro.
  - split; first done.
    split; first word.
    eapply has_encoding_from_app.
    replace (uint.nat (word.add off 1)) with (uint.nat off + 1)%nat by word.
    rewrite -drop_drop.
    rewrite Henc /= drop_0 //.
  - split; first done.
    split; first word.
    eapply has_encoding_from_app.
    replace (uint.nat (word.add off 1)) with (uint.nat off + 1)%nat by word.
    rewrite -drop_drop.
    rewrite Henc /= drop_0 //.
Qed.

(* This version of GetBytes consumes full ownership of the decoder to be able to
   give the full fraction to the returned slice *)
Theorem wp_Dec__GetBytes' stk E dec_v bs (n: u64) r s data :
  n = W64 (length bs) →
  {{{ is_dec dec_v (EncBytes bs :: r) s (DfracOwn 1) data ∗
      (∀ vs' : list u8, own_slice_small s byteT (DfracOwn 1) vs' -∗ own_slice s byteT (DfracOwn 1) vs') }}}
    Dec__GetBytes dec_v #n @ stk; E
  {{{ s', RET slice_val s'; own_slice s' byteT (DfracOwn 1) bs }}}.
Proof.
  iIntros (-> Φ) "(Hdec&Hclo) HΦ"; iNamed "Hdec".
  pose proof (has_encoding_length Henc).
  autorewrite with len in H.
  rewrite encoded_length_cons /= in H.
  wp_call.
  wp_load.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  wp_pures.
  iDestruct ("Hclo" with "[$]") as "Hs".
  wp_apply (wp_SliceSubslice_full with "Hs"); first by word.
  iIntros (s') "Hbs".
  wp_pures.
  wp_load; wp_store.
  iApply "HΦ". iModIntro.
  apply has_encoding_inv in Henc as [extra [Hdataeq _]].
  rewrite encode_cons /= -app_assoc in Hdataeq.
  iExactEq "Hbs".
  f_equal.
  rewrite -> subslice_drop_take by word.
  replace (uint.nat (word.add off (length bs)) - uint.nat off)%nat with (length bs) by word.
  rewrite Hdataeq.
  rewrite take_app_length' //; lia.
Qed.

Theorem wp_Dec__GetBytes stk E dec_v bs (n: u64) r s q data :
  n = W64 (length bs) →
  {{{ is_dec dec_v (EncBytes bs :: r) s q data }}}
    Dec__GetBytes dec_v #n @ stk; E
  {{{ q' s', RET slice_val s'; own_slice_small s' byteT q' bs ∗ is_dec dec_v r s q' data }}}.
Proof.
  iIntros (-> Φ) "Hdec HΦ"; iNamed "Hdec".
  pose proof (has_encoding_length Henc).
  autorewrite with len in H.
  rewrite encoded_length_cons /= in H.
  wp_call.
  wp_load.
  iDestruct (own_slice_small_sz with "Hs") as %Hsz.
  iMod (own_slice_small_persist with "Hs") as "#Hs".
  wp_pures.
  wp_apply (wp_SliceSubslice_small with "Hs"); first by word.
  iIntros (s') "Hbs".
  wp_pures.
  wp_load; wp_store.
  iApply "HΦ". iModIntro.
  apply has_encoding_inv in Henc as [extra [Hdataeq _]].
  rewrite encode_cons /= -app_assoc in Hdataeq.
  iSplitL "Hbs".
  { iExactEq "Hbs".
    f_equal.
    rewrite -> subslice_drop_take by word.
    replace (uint.nat (word.add off (length bs)) - uint.nat off)%nat with (length bs) by word.
    rewrite Hdataeq.
    rewrite take_app_length' //; lia.
  }
  iExists _, _; iFrame "∗#".
  iPureIntro.
  split_and!; auto; try len.
  replace (uint.nat (word.add off (length bs))) with (uint.nat off + uint.nat (length bs))%nat by word.
  rewrite -drop_drop.
  eapply has_encoding_from_app.
  rewrite Hdataeq.
  rewrite drop_app_length' //; word.
Qed.

(* TODO: use this to replace list_lookup_lt (it's much easier to remember) *)
Local Tactic Notation "list_elem" constr(l) constr(i) "as" simple_intropattern(x) :=
  let H := fresh "H" x "_lookup" in
  let i := lazymatch type of i with
           | nat => i
           | Z => constr:(Z.to_nat i)
           | u64 => constr:(uint.nat i)
           end in
  destruct (list_lookup_lt _ l i) as [x H];
  [ try solve [ len ]
  | ].

Theorem wp_Dec__GetInts stk E dec_v (xs: list u64) r (n: u64) s q data :
  length xs = uint.nat n →
  {{{ is_dec dec_v ((EncUInt64 <$> xs) ++ r) s q data }}}
    Dec__GetInts dec_v #n @ stk; E
  {{{ (s':Slice.t), RET slice_val s'; is_dec dec_v r s q data ∗ own_slice s' uint64T (DfracOwn 1) xs }}}.
Proof.
  iIntros (Hlen Φ) "Hdec HΦ".
  wp_rec; wp_pures.
  wp_apply (typed_mem.wp_AllocAt (slice.T uint64T)).
  { apply zero_val_ty', has_zero_slice_T. }
  iIntros (s_l) "Hsptr".
  wp_pures.
  wp_apply wp_ref_to; auto.
  iIntros (i_l) "Hi".
  wp_pures.
  wp_apply (wp_forUpto (λ i,
                        let done := take (uint.nat i) xs in
                        let todo := drop (uint.nat i) xs in
                        "Hdec" ∷ is_dec dec_v ((EncUInt64 <$> todo) ++ r) s q data ∗
                        "*" ∷ ∃ s, "Hsptr" ∷ s_l ↦[slice.T uint64T] (slice_val s) ∗
                                   "Hdone" ∷ own_slice s uint64T (DfracOwn 1) done
           )%I with "[] [Hi Hsptr Hdec]").
  - word.
  - clear Φ.
    iIntros (?) "!>".
    iIntros (Φ) "(HI&Hi&%Hlt) HΦ"; iNamed "HI".
    wp_pures.
    list_elem xs i as x.
    rewrite (drop_S _ _ _ Hx_lookup) /=.
    wp_apply (wp_Dec__GetInt with "Hdec"); iIntros "Hdec".
    wp_load.
    wp_apply (wp_SliceAppend with "Hdone"); iIntros (s') "Hdone".
    wp_store.
    iApply "HΦ". iFrame "Hsptr".
    replace (uint.nat (word.add i 1)) with (S (uint.nat i)) by word.
    erewrite take_S_r; eauto. by iFrame.
  - rewrite drop_0. iFrame "Hdec Hi".
    iExists Slice.nil.
    iFrame.
    rewrite take_0.
    iApply own_slice_nil; auto.
  - iIntros "(HI&Hi)"; iNamed "HI".
    wp_load.
    iApply "HΦ".
    rewrite -> take_ge, drop_ge by len.
    by iFrame "Hdone Hdec".
Qed.

(* special case where GetInts is the last thing and there are no more remaining
items to decode *)
Theorem wp_Dec__GetInts_complete stk E dec_v (xs: list u64) (n: u64) s q data :
  length xs = uint.nat n →
  {{{ is_dec dec_v (EncUInt64 <$> xs) s q data }}}
    Dec__GetInts dec_v #n @ stk; E
  {{{ (s':Slice.t), RET slice_val s'; is_dec dec_v [] s q data ∗ own_slice s' uint64T (DfracOwn 1) xs }}}.
Proof.
  iIntros (? Φ) "Hpre HΦ".
  wp_apply (wp_Dec__GetInts _ _ _ _ [] with "[Hpre]"); first by eauto.
  - rewrite app_nil_r //.
  - auto.
Qed.
*)

End goose_lang.

Typeclasses Opaque has_encoding.
