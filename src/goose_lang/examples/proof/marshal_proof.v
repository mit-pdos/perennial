From iris.proofmode Require Import coq_tactics reduction.
From Goose.github_com.tchajed Require Import marshal.
From Perennial.goose_lang Require Import wpc_proofmode.
From Perennial.goose_lang Require Import basic_triples encoding_proof.
From Perennial.goose_lang Require Import slice encoding.
From Perennial.goose_lang Require Import ffi.disk.
From Perennial.goose_lang Require Import ffi.disk_prelude.
Import uPred.

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

Definition encode1_length (e:encodable): nat :=
  match e with
  | EncUInt64 _ => 8%nat
  | EncUInt32 _ => 4%nat
  | EncBytes bs => length bs
  end.

Theorem encode1_length_ok e :
  encode1_length e = length $ encode1 e.
Proof.
  destruct e; auto.
Qed.

Fixpoint encode_length (es:Rec): nat :=
  match es with
  | [] => 0%nat
  | e::es => (encode1_length e + encode_length es)%nat
  end.

Hint Rewrite app_length @drop_length @take_length @fmap_length
     @replicate_length u64_le_bytes_length : len.
Hint Rewrite @vec_to_list_length : len.
Hint Rewrite @insert_length : len.
Hint Rewrite u64_le_length : len.

Ltac word := try lazymatch goal with
                 | |- envs_entails _ _ => iPureIntro
                 end; Integers.word.

Ltac len := autorewrite with len; try word.

Theorem encode_length_ok es :
  encode_length es = length $ encode es.
Proof.
  induction es; simpl; auto.
  rewrite IHes encode1_length_ok /encode.
  cbn [concat list_fmap fmap]; len.
Qed.

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
  length (encode [e]) = ltac:(let x := (eval hnf in (encode1_length e)) in exact x).
Proof.
  rewrite encode_singleton.
  destruct e; auto.
Qed.

Module EncM.
  Record t := mk { s: Slice.t;
                   off: loc; }.
  Definition to_val (x:t) : val :=
    (slice_val x.(s), #x.(off))%V.
  Lemma to_val_intro s (off: loc) :
    (slice_val s, #off)%V = to_val (mk s off).
  Proof.
    reflexivity.
  Qed.
End EncM.

Module DecM.
  Record t := mk { s: Slice.t;
                   off: loc; }.
  Definition to_val (x:t) : val :=
    (slice_val x.(s), #x.(off))%V.
  Lemma to_val_intro s (off: loc) :
    (slice_val s, #off)%V = to_val (mk s off).
  Proof.
    reflexivity.
  Qed.
End DecM.

Lemma loc_add_Sn l n :
  l +ₗ S n = (l +ₗ 1) +ₗ n.
Proof.
  rewrite loc_add_assoc.
  f_equal.
  lia.
Qed.

Theorem heap_array_to_list {Σ} {A} l0 (vs: list A) (P: loc -> A -> iProp Σ) :
  ([∗ map] l↦v ∈ heap_array l0 vs, P l v) ⊣⊢
  ([∗ list] i↦v ∈ vs, P (l0 +ₗ i) v).
Proof.
  (iInduction (vs) as [| v vs] "IH" forall (l0)).
  - simpl.
    rewrite big_sepM_empty.
    auto.
  - simpl.
    rewrite loc_add_0.
    rewrite big_sepM_union.
    { rewrite big_sepM_singleton.
      setoid_rewrite loc_add_Sn.
      iSpecialize ("IH" $! (l0 +ₗ 1)).
      iSplit.
      + iIntros "($&Hm)".
        iApply ("IH" with "Hm").
      + iIntros "($&Hl)".
        iApply ("IH" with "Hl").
    }
    symmetry.
    apply heap_array_map_disjoint; intros.
    apply (not_elem_of_dom (D := gset loc)).
    rewrite dom_singleton.
    intros ?%elem_of_singleton.
    rewrite loc_add_assoc in H2.
    apply loc_add_ne in H2; auto; lia.
Qed.

Section heap.
Context `{!heapG Σ}.
Context `{!crashG Σ}.
Existing Instance diskG0.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types z : Z.
Implicit Types s : Slice.t.
Implicit Types stk : stuckness.

Notation length := strings.length.

Hint Rewrite encode_app_length : len.
Hint Rewrite encode_singleton_length : len.
Hint Rewrite <- encode1_length_ok : len.

Definition is_enc (enc: EncM.t) (vs: Rec): iProp Σ :=
  ⌜int.val enc.(EncM.s).(Slice.sz) = 4096⌝ ∗
  let encoded := encode vs in
  let encoded_len := Z.of_nat (length encoded) in
  enc.(EncM.off) ↦ (Free #(U64 encoded_len)) ∗
  enc.(EncM.s).(Slice.ptr) ↦∗[byteT] fmap b2val encoded ∗
  ∃ (free: list u8),
    (enc.(EncM.s).(Slice.ptr) +ₗ encoded_len) ↦∗[byteT] fmap b2val free ∗
    ⌜(length encoded + length free)%nat = Z.to_nat 4096⌝.

Theorem wp_new_enc stk E :
  {{{ True }}}
    NewEnc #() @ stk; E
  {{{ enc, RET EncM.to_val enc; is_enc enc [] }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /NewEnc.
  rewrite /struct.buildStruct /Enc.S /=.
  wp_call.
  wp_apply wp_new_slice; [ word | ].
  iIntros (sl) "[Ha %]".
  rewrite replicate_length in H.
  change (int.nat 4096) with (Z.to_nat 4096) in H.
  wp_apply wp_alloc; auto.
  { repeat econstructor. }
  iIntros (l) "(Hl&_)".
  wp_steps.
  rewrite EncM.to_val_intro.
  iApply "HΦ".
  rewrite /is_enc.
  simpl.
  iSplitR; [ word | ].
  iFrame.
  rewrite array_nil.
  rewrite right_id left_id ?loc_add_0.
  iSplitL "Hl"; auto.
  iExists (replicate (int.nat 4096) (U8 0)).
  rewrite fmap_replicate; iFrame.
  len.
Qed.

Theorem wp_Enc__PutInt stk E enc vs (x: u64) :
  {{{ is_enc enc vs ∗ ⌜encode_length vs + 8 <= 4096⌝ }}}
    Enc__PutInt (EncM.to_val enc) #x @ stk; E
  {{{ RET #(); is_enc enc (vs ++ [EncUInt64 x]) }}}.
Proof.
  iIntros (Φ) "(Henc&%) HΦ".
  iDestruct "Henc" as "(%&Hoff&Henc&Hfree)".
  iDestruct "Hfree" as (free) "(Hfree&%)".
  wp_call.
  rewrite /struct.getField /Enc.S /=.
  wp_steps.
  wp_load.
  wp_steps.
  wp_apply wp_SliceSkip'.
  { iPureIntro.
    word. }
  wp_apply (wp_UInt64Put with "[Hfree]").
  { rewrite /is_slice /=.
    iSplitL; [ iSplitL | ].
    - iFramePtsTo by word.
    - len.
    - rewrite encode_length_ok in H.
      len.
  }
  iIntros "(Ha&%)".
  wp_steps.
  wp_load.
  wp_steps.
  wp_store.
  iApply "HΦ".
  cbn [slice_skip Slice.ptr].
  rewrite /is_enc.
  iSplitR; [ iPureIntro; auto | ].
  iSplitL "Hoff".
  {
    iFramePtsTo.
    repeat f_equal.
    apply word.unsigned_inj.
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
  iExists _; iFrame.
  iSplitL.
  { rewrite -fmap_drop.
    rewrite loc_add_assoc.
    iFramePtsTo.
    len.
    simpl; len.
  }
  rewrite encode_length_ok in H.
  len.
Qed.

Theorem wp_Enc__PutInt32 stk E enc vs (x: u32) :
  {{{ is_enc enc vs ∗ ⌜encode_length vs + 4 <= 4096⌝ }}}
    Enc__PutInt32 (EncM.to_val enc) #x @ stk; E
  {{{ RET #(); is_enc enc (vs ++ [EncUInt32 x]) }}}.
Proof.
  iIntros (Φ) "(Henc&%) HΦ".
  iDestruct "Henc" as "(%&Hoff&Henc&Hfree)".
  iDestruct "Hfree" as (free) "(Hfree&%)".
  wp_call.
  rewrite /struct.getField /Enc.S /=.
  wp_steps.
  wp_load.
  wp_steps.
  wp_apply wp_SliceSkip'.
  { iPureIntro.
    word. }
  wp_apply (wp_UInt32Put with "[Hfree]").
  { rewrite /is_slice /=.
    iSplitL; [ iSplitL | ].
    - iFramePtsTo by word.
    - len.
    - rewrite encode_length_ok in H.
      len.
  }
  iIntros "(Ha&%)".
  wp_steps.
  wp_load.
  wp_steps.
  wp_store.
  iApply "HΦ".
  cbn [slice_skip Slice.ptr].
  rewrite /is_enc.
  iSplitR; [ iPureIntro; auto | ].
  iSplitL "Hoff".
  {
    iFramePtsTo.
    repeat f_equal.
    apply word.unsigned_inj.
    len. }
  iDestruct (array_app with "Ha") as "[Hx Hfree]".
  iDestruct (array_app with "[$Henc Hx]") as "Henc".
  { iFramePtsTo by len. }
  iSplitL "Henc".
  { rewrite encode_app encode_singleton /=.
    rewrite /u64_le_bytes.
    rewrite -fmap_app.
    iFrame. }
  iExists _; iFrame.
  iSplitL.
  { rewrite -fmap_drop.
    rewrite loc_add_assoc.
    iFramePtsTo.
    rewrite encode_app encode_singleton.
    len.
    simpl; len.
  }
  rewrite encode_length_ok in H.
  len.
Qed.

Instance word_inhabited width (word: Interface.word width) : Inhabited word.
Proof.
  constructor.
  exact (word.of_Z 0).
Qed.

Instance Block0: Inhabited Block := _.

Definition list_to_block (l: list u8) : Block :=
  match decide (length l = Z.to_nat 4096) with
  | left H => eq_rect _ _ (list_to_vec l) _ H
  | _ => inhabitant
  end.

Lemma vec_to_list_of_list_eq_rect A (l: list A) n (H: length l = n) :
  vec_to_list (eq_rect _ _ (list_to_vec l) _ H) = l.
Proof.
  rewrite <- H; simpl.
  rewrite vec_to_list_of_list.
  auto.
Qed.

Definition list_to_block_to_vals l :
  length l = Z.to_nat 4096 ->
  Block_to_vals (list_to_block l) = b2val <$> l.
Proof.
  intros H.
  rewrite /list_to_block /Block_to_vals.
  rewrite decide_left.
  f_equal.
  rewrite vec_to_list_of_list_eq_rect; auto.
Qed.

Theorem big_sepL_impl A (f g: nat -> A -> iProp Σ) (l: list A) :
  (forall i x, f i x -∗ g i x) ->
  ([∗ list] i↦x ∈ l, f i x) -∗
  ([∗ list] i↦x ∈ l, g i x).
Proof.
  intros Himpl.
  apply big_opL_gen_proper; auto.
  typeclasses eauto.
Qed.

Lemma array_to_block l (bs: list byte) :
  length bs = Z.to_nat 4096 ->
  l ↦∗[byteT] (b2val <$> bs) -∗ mapsto_block l 1 (list_to_block bs).
Proof.
  rewrite /array /mapsto_block /Block_to_vals /list_to_block.
  iIntros (H) "Hl".
  rewrite decide_left.
  rewrite heap_array_to_list.
  rewrite !big_sepL_fmap.
  rewrite vec_to_list_of_list_eq_rect.
  setoid_rewrite Z.mul_1_l.
  iApply (big_sepL_impl with "Hl"); simpl.
  iIntros (i x) "[Hl _]".
  simpl.
  rewrite loc_add_0 right_id /b2val.
  iFrame.
Qed.

Theorem wp_Enc__Finish stk E enc vs :
  {{{ is_enc enc vs }}}
    Enc__Finish (EncM.to_val enc) @ stk; E
  {{{ s (extra: list u8), RET (slice_val s);
      mapsto_block s.(Slice.ptr) 1 (list_to_block $ encode vs ++ extra) ∗
      ⌜int.val s.(Slice.sz) = 4096⌝ ∗
     ⌜(encode_length vs + length extra)%Z = 4096⌝
  }}}.
Proof.
  iIntros (Φ) "Henc HΦ".
  wp_call.
  wp_call.
  iDestruct "Henc" as "(%&Hoff&Henc&Hfree)".
  iDestruct "Hfree" as (free) "(Hfree&%)".
  iDestruct (array_app with "[$Henc Hfree]") as "Hblock".
  { rewrite Z.mul_1_l.
    iFramePtsTo by len. }
  rewrite -fmap_app.
  iApply "HΦ".
  iSplit.
  { iApply (array_to_block with "Hblock").
    len. }
  rewrite encode_length_ok.
  len.
Qed.

Definition is_dec (dec: DecM.t) vs: iProp Σ :=
  ⌜int.val dec.(DecM.s).(Slice.sz) = 4096⌝ ∗
  ∃ (off: u64) (extra: list u8), dec.(DecM.off) ↦ Free #off ∗
    let encoded := encode vs in
  (dec.(DecM.s).(Slice.ptr) +ₗ int.val off) ↦∗[byteT]
    (b2val <$> (encoded ++ extra)) ∗
  ⌜(int.val off + length encoded + Z.of_nat (length extra))%Z = 4096⌝.

Theorem wp_NewDec stk E s vs (extra: list u8) :
  {{{ is_slice s byteT (b2val <$> encode vs ++ extra) ∗ ⌜int.val s.(Slice.sz)= 4096⌝ }}}
    NewDec (slice_val s) @ stk; E
  {{{ dec, RET (DecM.to_val dec); is_dec dec vs }}}.
Proof.
  iIntros (Φ) "(Hs&%) HΦ".
  iDestruct "Hs" as "(Ha&%)".
  autorewrite with len in H0.
  wp_call.
  wp_apply wp_alloc; [ | auto | iIntros (off) "Hoff" ].
  { repeat constructor. }
  wp_pures.
  rewrite DecM.to_val_intro.
  iApply "HΦ".
  rewrite /is_dec /=.
  iSplitR; eauto.
  iExists _, _; iFrame.
  iDestruct "Hoff" as "[[Hoff _] _]"; rewrite loc_add_0.
  iFrame.
  rewrite loc_add_0; iFrame.
  len.
Qed.

Theorem wp_Dec__GetInt stk E dec x vs :
  {{{ is_dec dec (EncUInt64 x::vs) }}}
    Dec__GetInt (DecM.to_val dec) @ stk; E
  {{{ RET #x; is_dec dec vs }}}.
Proof.
  iIntros (Φ) "Hdec HΦ".
  iDestruct "Hdec" as (Hdecsz off extra) "(Hoff&Hvs&%)".
  rewrite fmap_app.
  iDestruct (array_app with "Hvs") as "[Hxvs Hextra]".
  len.
  rewrite encode_cons fmap_app.
  iDestruct (array_app with "Hxvs") as "[Hx Hvs]".
  wp_call.
  wp_call.
  wp_load.
  wp_steps.
  wp_call.
  wp_load.
  wp_steps.
  wp_call.
  wp_store.
  wp_call.
  wp_apply wp_SliceSkip'; [ word | ].
  wp_apply (wp_UInt64Get' with "[Hx]").
  { iSplitL.
    - cbn [Slice.ptr slice_skip].
      rewrite Z.mul_1_l.
      iFramePtsTo by word.
    - simpl.
      simpl in H.
      word.
  }
  iIntros "Hx".
  cbn [Slice.ptr slice_skip].
  iApply "HΦ".
  rewrite /is_dec.
  iSplitR; eauto.
  iExists _, _; iFrame.
  rewrite !loc_add_assoc.
  iSplitL.
  { rewrite fmap_app.
    iApply array_app.
    iSplitR "Hextra".
    - iFramePtsTo.
      len.
      simpl.
      len.
    - rewrite loc_add_assoc.
      iFramePtsTo.
      len.
      simpl.
      len.
  }
  cbn [concat fmap list_fmap] in H.
  rewrite -encode_length_ok /= in H.
  rewrite -encode_length_ok.
  len.
Qed.

Theorem wp_Dec__GetInt32 stk E dec (x: u32) vs :
  {{{ is_dec dec (EncUInt32 x::vs) }}}
    Dec__GetInt32 (DecM.to_val dec) @ stk; E
  {{{ RET #x; is_dec dec vs }}}.
Proof.
  iIntros (Φ) "Hdec HΦ".
  iDestruct "Hdec" as (Hdecsz off extra) "(Hoff&Hvs&%)".
  rewrite fmap_app.
  iDestruct (array_app with "Hvs") as "[Hxvs Hextra]".
  len.
  rewrite encode_cons fmap_app.
  iDestruct (array_app with "Hxvs") as "[Hx Hvs]".
  wp_call.
  wp_call.
  wp_load.
  wp_steps.
  wp_call.
  wp_load.
  wp_steps.
  wp_call.
  wp_store.
  wp_call.
  wp_apply wp_SliceSkip'; [ word | ].
  wp_apply (wp_UInt32Get' with "[Hx]").
  { iSplitL.
    - cbn [Slice.ptr slice_skip].
      rewrite Z.mul_1_l.
      iFramePtsTo by word.
    - simpl.
      simpl in H.
      word.
  }
  iIntros "Hx".
  cbn [Slice.ptr slice_skip].
  iApply "HΦ".
  rewrite /is_dec.
  iSplitR; eauto.
  iExists _, _; iFrame.
  rewrite !loc_add_assoc.
  iSplitL.
  { rewrite fmap_app.
    iApply array_app.
    iSplitR "Hextra".
    - iFramePtsTo.
      len.
      simpl.
      len.
    - rewrite loc_add_assoc.
      iFramePtsTo.
      len.
      simpl.
      len.
  }
  cbn [concat fmap list_fmap] in H.
  rewrite -encode_length_ok /= in H.
  rewrite -encode_length_ok.
  len.
Qed.
End heap.
