From Goose.github_com.tchajed Require Import marshal.
From Perennial.goose_lang.lib Require Import encoding.
From Perennial.program_proof Require Import proof_prelude.

(* The specification for encoding is based on this encodable inductive, which
represents a single encodable bundle.

The high-level specs look like this:

{True}
  NewEnc()
{enc. is_enc enc []}

{is_enc enc es ∗ ⌜x fits⌝}
  enc.PutInt(x)
{is_enc enc (es ++ [EncUInt64 x])}

{is_enc enc es}
  enc.Finish()
{b. b ↦∗ to_bytes es}

The idea is that an Enc builds up a list of encoded items and maintains free
space (totalling 4096 bytes). The list of items is a dynamically-typed bundle,
an [encodable].

Symmetrically, Dec can extract an encoded list, popping elements (of the right
type) one at a time:

{b ↦∗ to_bytes es}
  NewDec(b)
{dec. is_dec dec es}

{is_dec (EncUInt64 x::es)}
  dec.GetInt()
{x. is_dec es}
 *)

Inductive encodable :=
| EncUInt64 (x:u64)
| EncUInt32 (x:u32)
| EncBytes (bs:list u8)
.

(* a record (not a descriptor) *)
Definition Rec := list encodable.

Definition encode1 (e:encodable) : list u8 :=
  match e with
  | EncUInt64 x => u64_le x
  | EncUInt32 x => u32_le x
  | EncBytes bs => bs
  end.

Definition encode (es:Rec): list u8 := concat (encode1 <$> es).

Hint Rewrite app_length @drop_length @take_length @fmap_length
     @replicate_length u64_le_bytes_length u32_le_bytes_length : len.
Hint Rewrite @vec_to_list_length : len.
Hint Rewrite @insert_length : len.
Hint Rewrite u64_le_length : len.

Ltac word := try lazymatch goal with
                 | |- envs_entails _ _ => iPureIntro
                 end; Integers.word.

Ltac len := autorewrite with len; try word.

Lemma encode_app es1 es2 :
  encode (es1 ++ es2) = encode es1 ++ encode es2.
Proof.
  rewrite /encode fmap_app concat_app //.
Qed.

Lemma encode_cons e es :
  encode (e::es) = encode1 e ++ encode es.
Proof.
  done.
Qed.

Lemma encode_app_length es1 es2 :
  length (encode (es1 ++ es2)) = (length (encode es1) + length (encode es2))%nat.
Proof.
  rewrite encode_app app_length //.
Qed.

Lemma encode_singleton e :
  encode [e] = encode1 e.
Proof.
  rewrite /encode /=.
  rewrite app_nil_r //.
Qed.

Lemma encode_singleton_length e :
  length (encode [e]) = match e with
                        | EncUInt64 _ => 8%nat
                        | EncUInt32 _ => 4%nat
                        | EncBytes bs => length bs
                        end.
Proof.
  rewrite encode_singleton.
  destruct e; auto.
Qed.

Module EncM.
  Record t := mk { s: Slice.t;
                   off: loc; }.
  Definition to_val (x:t) : val :=
    (slice_val x.(s), (#x.(off), #()))%V.
  Lemma to_val_intro s (off: loc) :
    (slice_val s, (#off, #()))%V = to_val (mk s off).
  Proof.
    reflexivity.
  Qed.
End EncM.

Module DecM.
  Record t := mk { s: Slice.t;
                   off: loc; }.
  Definition to_val (x:t) : val :=
    (slice_val x.(s), (#x.(off), #()))%V.
  Lemma to_val_intro s (off: loc) :
    (slice_val s, (#off, #()))%V = to_val (mk s off).
  Proof.
    reflexivity.
  Qed.
End DecM.

Section heap.
Context `{!heapG Σ}.
Implicit Types v : val.
Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Notation length := strings.length.

Hint Rewrite encode_app_length : len.
Hint Rewrite encode_singleton_length : len.

Definition EncSz (enc:EncM.t): u64 := enc.(EncM.s).(Slice.sz).

Theorem EncSz_fold enc : enc.(EncM.s).(Slice.sz) = EncSz enc.
Proof. reflexivity. Qed.

Hint Rewrite EncSz_fold : len.

Local Opaque load_ty store_ty.

Definition is_enc (enc: EncM.t) (vs: Rec) (free:Z): iProp Σ :=
  let encoded := encode vs in
  let encoded_len := Z.of_nat (length encoded) in
  enc.(EncM.off) ↦[uint64T] (#(U64 encoded_len)) ∗
  enc.(EncM.s).(Slice.ptr) ↦∗[byteT] (b2val <$> encoded) ∗
  (enc.(EncM.s).(Slice.ptr) +ₗ[byteT] encoded_len) ↦∗[byteT] fmap b2val (replicate (Z.to_nat free) (U8 0)) ∗
  ⌜(length encoded + Z.to_nat free)%nat = int.nat (EncSz enc)⌝.

Theorem wp_new_enc stk E (sz: u64) :
  {{{ True }}}
    NewEnc #sz @ stk; E
  {{{ enc, RET EncM.to_val enc; is_enc enc [] (int.val sz) ∗ ⌜EncSz enc = sz⌝ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /NewEnc.
  rewrite /struct.mk /Enc.S /=.
  wp_call.
  wp_apply wp_new_slice.
  { simpl; auto. }
  iIntros (sl) "Hs". iDestruct (is_slice_elim with "Hs") as "[Ha %]".
  rewrite replicate_length in H.
  wp_apply (typed_mem.wp_AllocAt uint64T); auto.
  iIntros (l) "Hl".
  wp_steps.
  rewrite EncM.to_val_intro.
  iApply "HΦ".
  rewrite /is_enc /EncSz /=.
  iSplitL.
  { rewrite array_nil.
    rewrite left_id ?loc_add_0.
    iFrame.
    rewrite fmap_replicate; iFrame.
    len. }
  iPureIntro.
  word.
Qed.

Theorem loc_add_assoc_ty l t z1 z2 :
  (l +ₗ[t] z1) +ₗ[t] z2 = l +ₗ[t] (z1 + z2).
Proof.
  rewrite loc_add_assoc.
  f_equal; lia.
Qed.

Theorem wp_Enc__PutInt stk E enc vs (x: u64) free :
  8 <= free ->
  {{{ is_enc enc vs free }}}
    Enc__PutInt (EncM.to_val enc) #x @ stk; E
  {{{ RET #(); is_enc enc (vs ++ [EncUInt64 x]) (free - 8) }}}.
Proof.
  iIntros (Hfree Φ) "Henc HΦ".
  iDestruct "Henc" as "(Hoff&Henc&Hfree&%)".
  rewrite /Enc__PutInt.
  wp_call.
  rewrite /struct.get /Enc.S /=.
  wp_steps.
  wp_load.
  wp_steps.
  wp_apply wp_SliceSkip'.
  { iPureIntro.
    len. }
  wp_apply (wp_UInt64Put with "[Hfree]").
  { rewrite /is_slice_small /=.
    iSplitL; [ iSplitL | ].
    - iFramePtsTo by word.
    - len.
    - len.
  }
  iIntros "(Ha&%)".
  wp_steps.
  wp_load.
  wp_pures.
  wp_store.
  iApply "HΦ".
  cbn [slice_skip Slice.ptr].
  rewrite /is_enc.
  iSplitL "Hoff".
  {
    iFramePtsTo.
    repeat f_equal.
    len.
  }
  iDestruct (array_app with "Ha") as "[Hx Hfree]".
  iDestruct (array_app with "[$Henc Hx]") as "Henc".
  { iFramePtsTo by len. }
  iSplitL "Henc".
  { rewrite encode_app encode_singleton /=.
    rewrite /u64_le_bytes.
    rewrite -fmap_app.
    iFrame. }
  iFrame.
  iSplitL.
  { rewrite -fmap_drop drop_replicate.
    rewrite loc_add_assoc_ty.
    iExactEq "Hfree".
    f_equal.
    - f_equal.
      f_equal.
      len.
    - f_equal.
      f_equal.
      lia.
  }
  len.
Qed.

Definition u64val (x: u64): val := #x.

Theorem length_encode_fmap_uniform (sz: nat) {A} (f: A -> encodable) l :
  (forall x, length (encode1 (f x)) = sz) ->
  length (encode (f <$> l)) = (sz * length l)%nat.
Proof.
  intros Hsz.
  induction l; simpl.
  - rewrite Nat.mul_0_r; auto.
  - rewrite encode_cons; autorewrite with len.
    rewrite Hsz.
    rewrite /fmap in IHl.
    lia.
Qed.

Lemma take_0 A (l: list A) : take 0%nat l = [].
Proof.
  reflexivity.
Qed.

Theorem wp_Enc__PutInts stk E enc vs (s:Slice.t) q (xs: list u64) free :
  8 * (Z.of_nat $ length xs) <= free ->
  {{{ is_enc enc vs free ∗ is_slice_small s uint64T q (u64val <$> xs) }}}
    Enc__PutInts (EncM.to_val enc) (slice_val s) @ stk; E
  {{{ RET #(); is_enc enc (vs ++ (EncUInt64 <$> xs)) (free - 8 * (Z.of_nat $ length xs)) ∗
      is_slice_small s uint64T q (u64val <$> xs) }}}.
Proof.
  iIntros (Hfree Φ) "(Henc&Hs) HΦ".
  rewrite /Enc__PutInts /ForSlice.
  wp_pures.
  wp_apply (wp_forSlice (λ i, is_enc enc
                                     (vs ++ (EncUInt64 <$> take (int.nat i) xs))
                                     (free - (8*int.val i)))%I
              with "[] [Henc $Hs]").
  - iIntros (i x) "!>".
    clear Φ.
    iIntros (Φ) "[Henc (%&%)] HΦ".
    apply list_lookup_fmap_inv in H0; destruct H0 as [xi [-> ?]].
    rewrite /u64val.
    wp_apply (wp_Enc__PutInt with "Henc").
    { apply lookup_lt_Some in H0.
      word.
    }
    iIntros "Henc"; iApply "HΦ".
    replace (int.nat (word.add i 1)) with (1 + int.nat i)%nat by word.
    erewrite take_S_r by eauto.
    rewrite -app_assoc fmap_app.
    iExactEq "Henc".
    f_equal.
    word.
  - rewrite take_0 app_nil_r.
    iExactEq "Henc".
    f_equal; word.
  - iIntros "(Henc&Hs)"; iApply "HΦ".
    iDestruct (is_slice_small_sz with "Hs") as %Hslen.
    rewrite fmap_length in Hslen.
    rewrite -> take_ge by lia.
    iFrame "Hs".
    iExactEq "Henc".
    f_equal; word.
Qed.

Theorem wp_Enc__PutInt32 stk E enc vs (x: u32) free :
  4 <= free ->
  {{{ is_enc enc vs free }}}
    Enc__PutInt32 (EncM.to_val enc) #x @ stk; E
  {{{ RET #(); is_enc enc (vs ++ [EncUInt32 x]) (free - 4) }}}.
Proof.
  iIntros (Hfree Φ) "Henc HΦ".
  iDestruct "Henc" as "(Hoff&Henc&Hfree&%)".
  wp_call.
  rewrite /struct.get /Enc.S /=.
  wp_steps.
  wp_load.
  wp_steps.
  wp_apply wp_SliceSkip'.
  { iPureIntro.
    len. }
  wp_apply (wp_UInt32Put with "[Hfree]").
  { rewrite /is_slice_small /=.
    iSplitL; [ iSplitL | ].
    - iFramePtsTo by word.
    - len.
    - len.
  }
  iIntros "(Ha&%)".
  wp_steps.
  wp_load.
  wp_store.
  iApply "HΦ".
  cbn [slice_skip Slice.ptr].
  rewrite /is_enc.
  iSplitL "Hoff".
  {
    iFramePtsTo.
    repeat f_equal.
    len. }
  iDestruct (array_app with "Ha") as "[Hx Hfree]".
  iDestruct (array_app with "[$Henc Hx]") as "Henc".
  { iFramePtsTo by len. }
  iSplitL "Henc".
  { rewrite encode_app encode_singleton /=.
    rewrite /u64_le_bytes.
    rewrite -fmap_app.
    iFrame. }
  iFrame.
  iSplitL.
  { rewrite -fmap_drop drop_replicate.
    rewrite loc_add_assoc_ty.
    iExactEq "Hfree".
    f_equal.
    - f_equal.
      f_equal.
      len.
    - f_equal.
      f_equal.
      lia.
  }
  len.
Qed.

Theorem wp_Enc__Finish stk E enc vs free :
  {{{ is_enc enc vs free }}}
    Enc__Finish (EncM.to_val enc) @ stk; E
  {{{ s, RET (slice_val s);
      let bs := b2val <$> encode vs ++ replicate (Z.to_nat free) (U8 0) in
      is_slice_small s byteT 1 bs ∗
      ⌜length bs = int.nat (EncSz enc)⌝ }}}.
Proof.
  iIntros (Φ) "Henc HΦ".
  wp_call.
  iDestruct "Henc" as "(Hoff&Henc&Hfree&%)".
  iDestruct (array_app with "[$Henc Hfree]") as "Hblock".
  { iExactEq "Hfree".
    f_equal.
    f_equal.
    rewrite ?Z.mul_1_l.
    len. }
  rewrite -fmap_app.
  iApply "HΦ".
  iSplit; len.
  iFrame; len.
Qed.

Theorem wp_Enc__Finish_complete stk E enc vs free :
  free = 0 ->
  {{{ is_enc enc vs free }}}
    Enc__Finish (EncM.to_val enc) @ stk; E
  {{{ s, RET (slice_val s);
      let bs := b2val <$> encode vs in
      is_slice_small s byteT 1 bs ∗
      ⌜length bs = int.nat (EncSz enc)⌝ }}}.
Proof.
  iIntros (Hfree Φ) "Henc HΦ".
  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (s) "(Hs&%)".
  rewrite Hfree replicate_0 app_nil_r in H |- *.
  by iApply ("HΦ" with "[$Hs]").
Qed.

Definition DecSz (dec: DecM.t): u64 := dec.(DecM.s).(Slice.sz).

Theorem DecSz_fold dec : ltac:(let rhs := constr:(DecSz dec) in
                               let lhs := (eval red in rhs) in
                               exact (lhs = rhs)).
Proof. reflexivity. Qed.

Hint Rewrite DecSz_fold : len.

Definition is_dec (dec: DecM.t) vs: iProp Σ :=
  ∃ (off: u64) (extra: list u8), dec.(DecM.off) ↦[uint64T] #off ∗
    let encoded := encode vs in
  (dec.(DecM.s).(Slice.ptr) +ₗ[byteT] int.val off) ↦∗[byteT]
    (b2val <$> (encoded ++ extra)) ∗
  ⌜(int.val off + length encoded + Z.of_nat (length extra))%Z = int.val (DecSz dec)⌝.

Theorem wp_NewDec stk E s vs (extra: list u8) :
  {{{ is_slice_small s byteT 1%Qp (b2val <$> encode vs ++ extra) }}}
    NewDec (slice_val s) @ stk; E
  {{{ dec, RET (DecM.to_val dec); is_dec dec vs ∗ ⌜DecSz dec = s.(Slice.sz)⌝ }}}.
Proof.
  iIntros (Φ) "(Hs&%) HΦ".
  wp_call.
  wp_apply typed_mem.wp_AllocAt; [ val_ty | iIntros (off) "Hoff" ].
  wp_pures.
  rewrite DecM.to_val_intro.
  iApply "HΦ".
  rewrite /is_dec /=.
  iSplitL; eauto.
  iExists _, _; iFrame.
  rewrite loc_add_0; iFrame.
  rewrite /DecSz; simpl.
  autorewrite with len in H; len.
Qed.

Theorem wp_Dec__GetInt stk E dec x vs :
  {{{ is_dec dec (EncUInt64 x::vs) }}}
    Dec__GetInt (DecM.to_val dec) @ stk; E
  {{{ RET #x; is_dec dec vs }}}.
Proof.
  iIntros (Φ) "Hdec HΦ".
  iDestruct "Hdec" as (off extra) "(Hoff&Hvs&%)".
  rewrite fmap_app.
  iDestruct (array_app with "Hvs") as "[Hxvs Hextra]".
  len.
  rewrite encode_cons fmap_app.
  iDestruct (array_app with "Hxvs") as "[Hx Hvs]".
  wp_call.
  wp_load.
  wp_steps.
  wp_load.
  wp_steps.
  wp_store.
  wp_call.
  wp_apply wp_SliceSkip'; [ now len | ].
  wp_apply (wp_UInt64Get' _ _ _ 1%Qp with "[Hx]").
  { iSplitL.
    - cbn [Slice.ptr slice_skip].
      rewrite Z.mul_1_l.
      iFramePtsTo by word.
    - simpl.
      simpl in H.
      len.
  }
  iIntros "Hx".
  cbn [Slice.ptr slice_skip].
  iApply "HΦ".
  rewrite /is_dec.
  iExists _, _; iFrame.
  rewrite !loc_add_assoc.
  iSplitL.
  { rewrite fmap_app.
    iApply array_app.
    iSplitR "Hextra".
    - iFramePtsTo.
      len.
      simpl.
      simpl in H.
      len.
    - rewrite loc_add_assoc.
      iFramePtsTo.
      len.
      simpl in H |- *.
      len.
  }
  cbn [concat fmap list_fmap] in H.
  rewrite encode_cons /= in H.
  len.
Qed.

Theorem wp_Dec__GetInt32 stk E dec (x: u32) vs :
  {{{ is_dec dec (EncUInt32 x::vs) }}}
    Dec__GetInt32 (DecM.to_val dec) @ stk; E
  {{{ RET #x; is_dec dec vs }}}.
Proof.
  iIntros (Φ) "Hdec HΦ".
  iDestruct "Hdec" as (off extra) "(Hoff&Hvs&%)".
  rewrite fmap_app.
  iDestruct (array_app with "Hvs") as "[Hxvs Hextra]".
  len.
  rewrite encode_cons fmap_app.
  iDestruct (array_app with "Hxvs") as "[Hx Hvs]".
  wp_call.
  wp_load.
  wp_steps.
  wp_load.
  wp_steps.
  wp_store.
  wp_call.
  wp_apply wp_SliceSkip'; [ now len | ].
  wp_apply (wp_UInt32Get' _ _ _ 1%Qp with "[Hx]").
  { iSplitL.
    - cbn [Slice.ptr slice_skip].
      rewrite Z.mul_1_l.
      iFramePtsTo by word.
    - simpl.
      simpl in H.
      len.
  }
  iIntros "Hx".
  cbn [Slice.ptr slice_skip].
  iApply "HΦ".
  rewrite /is_dec.
  iExists _, _; iFrame.
  rewrite !loc_add_assoc.
  iSplitL.
  { rewrite fmap_app.
    iApply array_app.
    iSplitR "Hextra".
    - iFramePtsTo.
      len.
      simpl in H |- *.
      word.
    - rewrite loc_add_assoc.
      iFramePtsTo.
      simpl.
      rewrite encode_cons /= in H.
      len.
  }
  cbn [concat fmap list_fmap] in H.
  rewrite encode_cons /= in H.
  len.
Qed.

Opaque load_ty.
Opaque store_ty.

Theorem u64_ptsto_untype l x :
  l ↦[uint64T] #x -∗ l ↦ #x.
Proof.
  iIntros "[H %]".
  inversion H; subst; clear H.
  inversion H1; subst.
  simpl.
  rewrite loc_add_0 right_id //.
Qed.

Theorem wp_Dec__GetInts stk E dec xs (n:u64) vs :
  {{{ is_dec dec ((EncUInt64 <$> xs) ++ vs) ∗ ⌜int.val n = length xs⌝}}}
    Dec__GetInts (DecM.to_val dec) #n @ stk; E
  {{{ s, RET slice_val s; is_dec dec vs ∗ is_slice s uint64T 1%Qp (u64val <$> xs) }}}.
Proof.
  rewrite /Dec__GetInts.
  iIntros (Φ) "(Hdec&%) HΦ".
  wp_pures.
  wp_apply (typed_mem.wp_AllocAt (slice.T uint64T)); auto.
  (* TODO: fix how this works so auto solves the goal  *)
  { auto with val_ty. }
  iIntros (l) "Hl".
  rewrite zero_slice_val.
  wp_pures.
  wp_apply typed_mem.wp_ref_to; auto.
  iIntros (l__i) "Hli".
  wp_let.
  wp_apply (wp_forUpto (λ x,
                        let num := int.nat x in
                        let done_xs: list u64 := take num xs in
                        let remaining_xs: list u64 := drop num xs in
                        is_dec dec ((EncUInt64 <$> remaining_xs) ++ vs) ∗
                               ∃ s, l ↦[slice.T uint64T] (slice_val s) ∗
                                    is_slice s uint64T 1%Qp (u64val <$> done_xs))%I with "[] [Hdec Hl Hli]").
  - iIntros (i) "!>".
    clear Φ.
    iIntros (Φ) "([Hdec Hpre] & Hli & %) HΦ".
    iDestruct "Hpre" as (s) "(Hl&Hs)".
    wp_pures.
    assert (exists x, xs !! int.nat i = Some x) as Hlookup.
    { apply list_lookup_lt; word. }
    destruct Hlookup as [x Hlookup].
    wp_apply (wp_Dec__GetInt with "[Hdec]").
    { erewrite drop_S by eauto.
      rewrite fmap_cons.
      iFrame. }
    fold (@app encodable).
    iIntros "Hdec".
    wp_load.
    iDestruct (is_slice_sz with "Hs") as %Hsz.
    autorewrite with len in Hsz.
    wp_apply (wp_SliceAppend with "[$Hs]"); first by auto.
    { iPureIntro; split; [ word | auto ]. }
    iIntros (s') "Hs".
    wp_apply (wp_StoreAt with "Hl"); [ val_ty | iIntros "Hl" ].
    wp_pures.
    rewrite /Continue.
    iApply "HΦ".
    iFrame.
    replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
    iFrame.
    iExists s'; iFrame.
    erewrite take_S_r; eauto.
    rewrite fmap_app; simpl.
    iFrame.
  - rewrite drop_0.
    iFrame.
    iDestruct (u64_ptsto_untype with "Hli") as "Hli".
    iFrame.
    iExists (Slice.mk null (U64 0) (U64 0)); iFrame.
    rewrite take_0 fmap_nil.
    iApply is_slice_zero.
  - iIntros "[(Hdec&Hslice) Hli]".
    iDestruct "Hslice" as (s) "[Hl Hs]".
    wp_pures.
    wp_load.
    iApply "HΦ".
    rewrite -> take_ge by word.
    rewrite -> drop_ge by word.
    rewrite fmap_nil app_nil_l.
    iFrame.
Qed.

End heap.
