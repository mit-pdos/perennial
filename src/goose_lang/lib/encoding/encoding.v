From Perennial.Helpers Require Import ListLen.

From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From Perennial.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export
     lang notation array typing struct
     tactics lifting proofmode.
From Perennial.goose_lang Require Import slice.
From Perennial.goose_lang.lib Require Export encoding.impl.

Set Default Proof Using "Type".

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Section heap.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types z : Z.
Implicit Types off : nat.

Lemma word_sru_0 width (word: Interface.word width) (ok: word.ok word)
      (x: word) s : uint.Z s = 0 -> word.sru x s = x.
Proof.
  intros.
  apply word.unsigned_inj.
  rewrite word.unsigned_sru.
  - rewrite H.
    rewrite Z.shiftr_0_r.
    unfold word.wrap.
    rewrite word.wrap_unsigned.
    auto.
  - rewrite H.
    apply word.width_pos.
Qed.

Theorem word_wrap_wrap `{word1: Interface.word width1} `{word2: Interface.word width2}
        {ok1: word.ok word1}
        {ok2: word.ok word2} z :
  width1 <= width2 ->
  word.wrap (word:=word1) (word.wrap (word:=word2) z) = word.wrap (word:=word1) z.
Proof.
  unfold word.wrap; intros.
  pose proof (@word.width_pos width1 _ _).
  pose proof (@word.width_pos width2 _ _).
  pose proof (Z.pow_pos_nonneg 2 width1 ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 width2 ltac:(lia) ltac:(lia)).
  rewrite <- Znumtheory.Zmod_div_mod; try lia.
  exists (2 ^ (width2 - width1)).
  rewrite <- Z.pow_add_r; try lia.
  f_equal.
  lia.
Qed.

Theorem word_wrap_wrap' `{word1: Interface.word width1} `{word2: Interface.word width2}
        {ok1: word.ok word1}
        {ok2: word.ok word2} z :
  width2 <= width1 ->
  word.wrap (word:=word1) (word.wrap (word:=word2) z) = word.wrap (word:=word2) z.
Proof.
  unfold word.wrap; intros.
  pose proof (@word.width_pos width1 _ _).
  pose proof (@word.width_pos width2 _ _).
  pose proof (Z.pow_pos_nonneg 2 width1 ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 width2 ltac:(lia) ltac:(lia)).
  rewrite (Zmod_small _ (2 ^ width1)); first done.
  split; try lia.
  assert (z `mod` 2 ^ width2 < 2 ^ width2); try lia.
  assert (2 ^ width2 ≤ 2 ^ width1); try lia.
  eapply Z.pow_le_mono_r; lia.
Qed.

Hint Rewrite word.unsigned_of_Z : word.
Hint Rewrite word.unsigned_sru : word.

Theorem word_byte_extract (x:u32) k :
  0 <= k < 4 ->
  word.of_Z (uint.Z x ≫ (k*8)) = W8 (uint.Z (word.sru x (W32 (k*8)))).
Proof.
  intros.
  apply word.unsigned_inj.
  unfold W8.
  autorewrite with word.
  rewrite word.unsigned_sru;
    rewrite unsigned_U32.
  { rewrite word_wrap_wrap; last lia.
    rewrite [word.wrap (k * _)]wrap_small; last lia.
    reflexivity.
  }
  rewrite wrap_small; lia.
Qed.

Theorem word64_byte_extract (x:u64) k :
  0 <= k < 8 ->
  word.of_Z (uint.Z x ≫ (k*8)) = W8 (uint.Z (word.sru x (W64 (k*8)))).
Proof.
  intros.
  apply word.unsigned_inj.
  unfold W8.
  autorewrite with word.
  rewrite word.unsigned_sru;
    rewrite unsigned_U64.
  { rewrite word_wrap_wrap; last lia.
    rewrite [word.wrap (k * _)]wrap_small; last lia.
    reflexivity.
  }
  rewrite wrap_small; lia.
Qed.

Theorem u32_le_to_sru (x: u32) :
  b2val <$> u32_le x =
  cons #(W8 (uint.Z (word.sru x (W32 (0%nat * 8)))))
       (cons #(W8 (uint.Z (word.sru x (W32 (1%nat * 8)))))
             (cons #(W8 (uint.Z (word.sru x (W32 (2%nat * 8)))))
                   (cons #(W8 (uint.Z (word.sru x (W32 (3%nat * 8)))))
                         nil))).
Proof.
  rewrite /b2val.
  cbv [u32_le fmap list_fmap LittleEndian.split HList.tuple.to_list List.map].
  rewrite -word_byte_extract; last lia.
  rewrite -word_byte_extract; last lia.
  rewrite -word_byte_extract; last lia.
  rewrite -word_byte_extract; last lia.
  reflexivity.
Qed.

Theorem wp_EncodeUInt32 (l: loc) (x: u32) vs s E :
  {{{ ▷ l ↦∗[byteT] vs ∗ ⌜ length vs = w32_bytes ⌝ }}}
    EncodeUInt32 #x #l @ s ; E
  {{{ RET #(); l ↦∗[byteT] (b2val <$> u32_le x) }}}.
Proof.
  iIntros (Φ) "(>Hl & %) HΦ".
  unfold EncodeUInt32.
  repeat (destruct vs; simpl in H; [ congruence | ]).
  destruct vs; [ | simpl in H; congruence ]; clear H.
  remember u8T.
  simpl.
  cbv [array].
  iDestruct "Hl" as "(Hv&Hv0&Hv1&Hv2&_)".
  wp_pures.
  rewrite ?Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv0]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv0".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv1]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv1".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv2]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv2".

  iApply "HΦ".
  change (W32 8) with (W32 (1 * 8)).
  rewrite -?word_byte_extract; try lia.
  subst.
  simpl.
  iFrame.
Qed.

Definition u64_le_bytes (x: u64) : list val :=
  b2val <$> u64_le x.

Lemma u64_le_bytes_length x : length (u64_le_bytes x) = w64_bytes.
Proof.
  rewrite fmap_length //.
Qed.

Theorem wp_EncodeUInt64 (l: loc) (x: u64) vs stk E :
  {{{ ▷ l ↦∗[byteT] vs ∗ ⌜ length vs = w64_bytes ⌝ }}}
    EncodeUInt64 #x #l @ stk ; E
  {{{ RET #(); l ↦∗[byteT] (b2val <$> u64_le x) }}}.
Proof.
  iIntros (Φ) "(>Hl & %) HΦ".
  unfold EncodeUInt64.
  repeat (destruct vs; simpl in H; [ congruence | ]).
  destruct vs; [ | simpl in H; congruence ]; clear H.
  remember u8T.
  simpl.
  cbv [array].
  iDestruct "Hl" as "(Hv&Hv0&Hv1&Hv2&Hv3&Hv4&Hv5&Hv6&_)".
  wp_pures.
  rewrite ?Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv0]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv0".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv1]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv1".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv2]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv2".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv3]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv3".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv4]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv4".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv5]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv5".

  wp_pures.
  rewrite Z.mul_1_l.
  wp_apply (wp_StoreAt with "[Hv6]").
  { subst; repeat constructor. }
  { subst; iFrame. }
  iIntros "Hv6".

  iApply "HΦ".
  change (W64 8) with (W64 (1 * 8)).
  rewrite -?word64_byte_extract; try lia.
  subst.
  simpl.
  iFrame.
Qed.

Theorem wp_UInt64Put stk E s x vs :
  length vs >= w64_bytes →
  {{{ own_slice_small s byteT (DfracOwn 1) vs }}}
    UInt64Put (slice_val s) #x @ stk; E
  {{{ RET #(); own_slice_small s byteT (DfracOwn 1) (u64_le_bytes x ++ (drop w64_bytes vs)) }}}.
Proof.
  iIntros (? Φ) "Hsl HΦ".
  wp_lam.
  wp_let.
  wp_lam.
  wp_pures.
  rewrite /own_slice_small. iDestruct "Hsl" as "(Hptr&%)".
  iDestruct (array_split 8 with "Hptr") as "[Henc Hrest]"; [ lia .. | ].
  wp_apply (wp_EncodeUInt64 with "[$Henc]").
  { iPureIntro.
    rewrite take_length; lia. }
  iIntros "Henc".
  change (Z.to_nat 8) with 8%nat.
  iDestruct (array_app with "[$Henc $Hrest]") as "Htogether".
  iApply "HΦ".
  iFrame.
  rewrite app_length drop_length u64_le_bytes_length.
  iPureIntro.
  lia.
Qed.

Definition u32_le_bytes (x: u32) : list val :=
  b2val <$> u32_le x.

Lemma u32_le_bytes_length x : length (u32_le_bytes x) = w32_bytes.
Proof.
  rewrite fmap_length //.
Qed.

Theorem wp_UInt32Put stk E s (x: u32) vs :
  length vs >= w32_bytes →
  {{{ own_slice_small s byteT (DfracOwn 1) vs }}}
    UInt32Put (slice_val s) #x @ stk; E
  {{{ RET #(); own_slice_small s byteT (DfracOwn 1) (u32_le_bytes x ++ (drop w32_bytes vs)) }}}.
Proof.
  iIntros (? Φ) "Hsl HΦ".
  wp_lam.
  wp_let.
  wp_lam.
  wp_pures.
  rewrite /own_slice_small.
  iDestruct "Hsl" as "(Hptr&%)".
  iDestruct (array_split 4 with "Hptr") as "[Henc Hrest]"; [ lia .. | ].
  wp_apply (wp_EncodeUInt32 with "[$Henc]").
  { iPureIntro.
    rewrite take_length; lia. }
  iIntros "Henc".
  change (Z.to_nat 4) with 4%nat.
  iDestruct (array_app with "[$Henc $Hrest]") as "Htogether".
  iApply "HΦ".
  iFrame.
  rewrite app_length drop_length u32_le_bytes_length.
  iPureIntro.
  lia.
Qed.

Hint Rewrite word.unsigned_or_nowrap : word.
Hint Rewrite word.unsigned_slu : word.

Ltac eval_term t :=
  let t' := (eval cbv in t) in change t with t'.

Ltac eval_u32 :=
  match goal with
  | |- context[uint.Z (W32 ?z)] =>
    rewrite  (Z_u32 z ltac:(lia))
  end.

Ltac eval_u64 :=
  match goal with
  | |- context[uint.Z (W64 ?z)] =>
    rewrite  (Z_u64 z ltac:(lia))
  end.

Theorem u8_to_from_u32 (x:w32) :
  uint.Z (W32 (uint.Z (W8 (uint.Z x)))) =
  uint.Z x `mod` 2 ^ 8.
Proof.
  unfold W8, W32.
  autorewrite with word.
  rewrite word.unsigned_of_Z.
  rewrite word_wrap_wrap'; last lia.
  reflexivity.
Qed.

Lemma val_u8_to_u32 (x:w8) :
  uint.Z (W32 (uint.Z x)) = uint.Z x.
Proof.
  unfold W32.
  rewrite word.unsigned_of_Z.
  pose proof (word.unsigned_range x).
  rewrite wrap_small; lia.
Qed.

Lemma val_u8_to_u64 (x:w8) :
  uint.Z (W64 (uint.Z x)) = uint.Z x.
Proof.
  unfold W64.
  rewrite word.unsigned_of_Z.
  pose proof (word.unsigned_range x).
  rewrite wrap_small; lia.
Qed.

Lemma word_wrap_8_nonneg (x : Z) : 0 ≤ x -> 0 ≤ word.wrap (width:=8) x.
Proof. rewrite /word.wrap. lia. Qed.

Lemma word_wrap_32_nonneg (x : Z) : 0 ≤ x -> 0 ≤ word.wrap (width:=32) x.
Proof. rewrite /word.wrap. lia. Qed.

Lemma word_wrap_64_nonneg (x : Z) : 0 ≤ x -> 0 ≤ word.wrap (width:=64) x.
Proof. rewrite /word.wrap. lia. Qed.

Lemma unsigned_8_nonneg (x : u8) : 0 ≤ uint.Z x.
Proof. pose proof (word.unsigned_range x). lia. Qed.

Lemma unsigned_32_nonneg (x : u32) : 0 ≤ uint.Z x.
Proof. pose proof (word.unsigned_range x). lia. Qed.

Lemma unsigned_64_nonneg (x : u64) : 0 ≤ uint.Z x.
Proof. pose proof (word.unsigned_range x). lia. Qed.

Lemma word_wrap_lt_8 (x : Z) n :
  8 ≤ n ->
  word.wrap (width:=8) x < 2^n.
Proof.
  rewrite /word.wrap; intros.
  assert (x `mod` 2^8 < 2^8) by (apply Z_mod_lt; lia).
  assert (2 ^ 8 ≤ 2 ^ n); try lia.
  eapply Z.pow_le_mono_r; lia.
Qed.

Lemma word_wrap_lt_32 (x : Z) n :
  0 ≤ x < 2^n ->
  word.wrap (width:=32) x < 2^n.
Proof.
  rewrite /word.wrap; intros.
  assert (x `mod` 2^32 ≤ x); lia.
Qed.

Lemma word_wrap_lt_64 (x : Z) n :
  0 ≤ x < 2^n ->
  word.wrap (width:=64) x < 2^n.
Proof.
  rewrite /word.wrap; intros.
  assert (x `mod` 2^64 ≤ x); lia.
Qed.

Lemma Zlor_nonneg a b :
  0 ≤ a ->
  0 ≤ b ->
  0 ≤ Z.lor a b.
Proof.
  intros; apply Z.lor_nonneg; eauto.
Qed.

Lemma Zlor_lt width (x y : Z) :
  0 ≤ x < 2^width ->
  0 ≤ y < 2^width ->
  Z.lor x y < 2^width.
Proof.
  intuition idtac.
  destruct (decide (x = 0)).
  { subst. rewrite Z.lor_0_l. lia. }
  destruct (decide (y = 0)).
  { subst. rewrite Z.lor_0_r. lia. }
  destruct (decide (Z.lor x y = 0)).
  { lia. }
  edestruct (Z.log2_spec (Z.lor x y)).
  { assert (0 ≤ Z.lor x y) by (eapply Zlor_nonneg; lia). lia. }
  rewrite Z.log2_lor in H4; try lia.
  eapply Z.log2_lt_pow2 in H2; try lia.
  eapply Z.log2_lt_pow2 in H3; try lia.
  assert (Z.succ (Z.log2 x `max` Z.log2 y) ≤ width) by lia.
  assert (2 ^ Z.succ (Z.log2 x `max` Z.log2 y) ≤ 2 ^ width); try lia.
  eapply Z.pow_le_mono_r; lia.
Qed.

Lemma Zshiftl_lt width (x : Z) :
  8 ≤ width ->
  x < 2^(width-8) ->
  Z.shiftl x 8 < 2^width.
Proof.
  rewrite Z.shiftl_mul_pow2; try lia.
  intros.
  rewrite Z.pow_sub_r in H0; try lia.
Qed.

Lemma Zshiftl_nonneg a b : 0 ≤ a -> 0 ≤ Z.shiftl a b.
Proof. intros. apply Z.shiftl_nonneg. eauto. Qed.

Lemma Zshiftr_nonneg a b : 0 ≤ a -> 0 ≤ Z.shiftr a b.
Proof. intros. apply Z.shiftr_nonneg. eauto. Qed.

Ltac bit_bound_nonneg :=
  eapply unsigned_8_nonneg ||
  eapply unsigned_32_nonneg ||
  eapply unsigned_64_nonneg ||
  eapply word_wrap_8_nonneg ||
  eapply word_wrap_32_nonneg ||
  eapply word_wrap_64_nonneg ||
  eapply Zlor_nonneg ||
  eapply Zshiftl_nonneg ||
  eapply Zshiftr_nonneg.

Ltac bit_bound_lt :=
  eapply word_wrap_lt_8 ||
  eapply word_wrap_lt_32 ||
  eapply word_wrap_lt_64 ||
  eapply Zlor_lt ||
  eapply Zshiftl_lt.

Ltac bit_bound :=
  repeat ( split || bit_bound_nonneg || bit_bound_lt || eauto || lia ).

Lemma word_wrap_32_Zlor (x y : Z) :
  0 ≤ x < 2^32 ->
  0 ≤ y < 2^32 ->
  word.wrap (width:=32) (Z.lor x y) = Z.lor x y.
Proof.
  intros.
  rewrite wrap_small; eauto.
  intuition bit_bound.
Qed.

Lemma word_wrap_32_Zshiftl (x : Z) :
  0 ≤ x < 2^24 ->
  word.wrap (width:=32) (Z.shiftl x 8) = Z.shiftl x 8.
Proof.
  intros.
  rewrite wrap_small; eauto.
  intuition bit_bound.
Qed.

Lemma word_wrap_64_Zlor (x y : Z) :
  0 ≤ x < 2^64 ->
  0 ≤ y < 2^64 ->
  word.wrap (width:=64) (Z.lor x y) = Z.lor x y.
Proof.
  intros.
  rewrite wrap_small; eauto.
  intuition bit_bound.
Qed.

Lemma word_wrap_64_Zshiftl (x : Z) :
  0 ≤ x < 2^56 ->
  word.wrap (width:=64) (Z.shiftl x 8) = Z.shiftl x 8.
Proof.
  intros.
  rewrite wrap_small; eauto.
  intuition bit_bound.
Qed.

Theorem decode_encode (x : w32) :
  word.or (W32 (uint.Z (@word.of_Z 8 _ (uint.Z x))))
        (word.slu
           (word.or (W32 (uint.Z (@word.of_Z 8 _ (uint.Z x ≫ 8))))
              (word.slu
                 (word.or (W32 (uint.Z (@word.of_Z 8 _ ((uint.Z x ≫ 8) ≫ 8))))
                    (word.slu (W32 (uint.Z (@word.of_Z 8 _ (((uint.Z x ≫ 8) ≫ 8) ≫ 8)))) (W32 8)))
                 (W32 8))) (W32 8)) = x.
Proof.
  apply word.unsigned_inj.
  pose proof (u32_le_to_word x).
  cbv [le_to_u32 u32_le map LittleEndian.combine LittleEndian.split length Datatypes.HList.tuple.to_list Datatypes.HList.tuple.of_list PrimitivePair.pair._1 PrimitivePair.pair._2] in H.
  rewrite Z.shiftl_0_l in H.
  rewrite Z.lor_0_r in H.
  rewrite ?word.unsigned_of_Z in H.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u32; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u32; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u32; try lia.
  rewrite ?val_u8_to_u32.
  rewrite <- H at 5; clear H.
  rewrite ?word.unsigned_of_Z.
  repeat ( rewrite word_wrap_wrap'; last by lia ).
  repeat (( rewrite -> word_wrap_32_Zlor by intuition bit_bound ) ||
          ( rewrite -> word_wrap_32_Zshiftl by intuition bit_bound )).
  reflexivity.
Qed.

Theorem decode_encode64 (x : w64) :
  word.or (W64 (uint.Z (@word.of_Z 8 _ (uint.Z x))))
        (word.slu
           (word.or (W64 (uint.Z (@word.of_Z 8 _ (uint.Z x ≫ 8))))
              (word.slu
                 (word.or (W64 (uint.Z (@word.of_Z 8 _ ((uint.Z x ≫ 8) ≫ 8))))
                    (word.slu
                       (word.or (W64 (uint.Z (@word.of_Z 8 _ (((uint.Z x ≫ 8) ≫ 8) ≫ 8))))
                          (word.slu
                             (word.or (W64 (uint.Z (@word.of_Z 8 _ ((((uint.Z x ≫ 8) ≫ 8) ≫ 8) ≫ 8))))
                                (word.slu
                                   (word.or (W64 (uint.Z (@word.of_Z 8 _ (((((uint.Z x ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8))))
                                      (word.slu
                                         (word.or (W64 (uint.Z (@word.of_Z 8 _ ((((((uint.Z x ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8))))
                                            (word.slu (W64 (uint.Z (@word.of_Z 8 _ (((((((uint.Z x ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8) ≫ 8)))) (W64 8)))
                                         (W64 8)))
                                    (W64 8)))
                              (W64 8)))
                        (W64 8)))
                  (W64 8)))
            (W64 8)) = x.
Proof.
  apply word.unsigned_inj.
  pose proof (u64_le_to_word x).
  cbv [le_to_u64 u64_le map LittleEndian.combine LittleEndian.split length Datatypes.HList.tuple.to_list Datatypes.HList.tuple.of_list PrimitivePair.pair._1 PrimitivePair.pair._2] in H.
  rewrite Z.shiftl_0_l in H.
  rewrite Z.lor_0_r in H.
  rewrite ?word.unsigned_of_Z in H.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u64; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u64; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u64; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u64; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u64; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u64; try lia.
  rewrite word.unsigned_or_nowrap.
  rewrite word.unsigned_slu; eval_u64; try lia.
  rewrite ?val_u8_to_u64.
  rewrite <- H at 9; clear H.
  rewrite ?word.unsigned_of_Z.
  repeat ( rewrite word_wrap_wrap'; last by lia ).
  repeat (( rewrite -> word_wrap_64_Zlor by intuition bit_bound ) ||
          ( rewrite -> word_wrap_64_Zshiftl by intuition bit_bound )).
  reflexivity.
Qed.

Theorem wp_DecodeUInt32 (l: loc) q (x: u32) s E :
  {{{ ▷ l ↦∗[byteT]{q} (b2val <$> u32_le x) }}}
    DecodeUInt32 #l @ s ; E
  {{{ RET #x; l ↦∗[byteT]{q} (b2val <$> u32_le x) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  cbv [u32_le fmap list_fmap LittleEndian.split HList.tuple.to_list List.map].
  rewrite ?array_cons ?loc_add_assoc.
  iDestruct "Hl" as "(Hl0&Hl1&Hl2&Hl3&Hemp)".
  rewrite /DecodeUInt32.
  remember u8T.
  wp_pures.
  wp_apply (wp_LoadAt with "[Hl0]"); [ subst; iFrame | iIntros "Hl0" ].
  wp_apply (wp_LoadAt with "[Hl1]"); [ subst; iFrame | iIntros "Hl1" ].
  wp_apply (wp_LoadAt with "[Hl2]"); [ subst; iFrame | iIntros "Hl2" ].
  wp_apply (wp_LoadAt with "[Hl3]"); [ subst; iFrame | iIntros "Hl3" ].
  wp_pures.
  rewrite decode_encode.
  iApply "HΦ".
  subst; simpl.
  by iFrame.
Qed.

Theorem wp_DecodeUInt64 (l: loc) q (x: u64) s E :
  {{{ ▷ l ↦∗[byteT]{q} (b2val <$> u64_le x) }}}
    DecodeUInt64 #l @ s ; E
  {{{ RET #x; l ↦∗[byteT]{q} (b2val <$> u64_le x) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  cbv [u64_le fmap list_fmap LittleEndian.split HList.tuple.to_list List.map].
  rewrite ?array_cons ?loc_add_assoc.
  iDestruct "Hl" as "(Hl0&Hl1&Hl2&Hl3&Hl4&Hl5&Hl6&Hl7&Hemp)".
  rewrite /DecodeUInt64.
  remember u8T.
  wp_pures.
  wp_apply (wp_LoadAt with "[Hl0]"); [ subst; iFrame | iIntros "Hl0" ].
  wp_apply (wp_LoadAt with "[Hl1]"); [ subst; iFrame | iIntros "Hl1" ].
  wp_apply (wp_LoadAt with "[Hl2]"); [ subst; iFrame | iIntros "Hl2" ].
  wp_apply (wp_LoadAt with "[Hl3]"); [ subst; iFrame | iIntros "Hl3" ].
  wp_apply (wp_LoadAt with "[Hl4]"); [ subst; iFrame | iIntros "Hl4" ].
  wp_apply (wp_LoadAt with "[Hl5]"); [ subst; iFrame | iIntros "Hl5" ].
  wp_apply (wp_LoadAt with "[Hl6]"); [ subst; iFrame | iIntros "Hl6" ].
  wp_apply (wp_LoadAt with "[Hl7]"); [ subst; iFrame | iIntros "Hl7" ].
  wp_pures.
  rewrite decode_encode64.
  iApply "HΦ".
  subst; simpl.
  by iFrame.
Qed.

Theorem wp_UInt64Get stk E s q (x: u64) vs :
  {{{ own_slice_small s byteT q vs ∗ ⌜take 8 vs = u64_le_bytes x⌝ }}}
    UInt64Get (slice_val s) @ stk; E
  {{{ RET #x; own_slice_small s byteT q (u64_le_bytes x ++ drop 8 vs) }}}.
Proof.
  iIntros (Φ) "[Hs %] HΦ".
  assert (vs = u64_le_bytes x ++ drop 8 vs).
  { rewrite -{1}(take_drop 8 vs).
    congruence. }
  rewrite [vs in own_slice_small _ _ _ vs](H0).
  wp_call.
  wp_apply wp_slice_ptr.
  rewrite /own_slice_small.
  iDestruct "Hs" as "(Hptr&%)".
  iDestruct (array_app with "Hptr") as "[Htake Hrest]"; try lia;
    rewrite u64_le_bytes_length.
  wp_apply (wp_DecodeUInt64 with "[$Htake]").
  iIntros "Htake".
  iDestruct (array_app with "[$Htake Hrest]") as "Hptr".
  { rewrite fmap_length u64_le_length.
    iFrame. }
  iApply "HΦ".
  iFrame.
  iPureIntro.
  rewrite app_length u64_le_bytes_length drop_length in H1 |- *.
  lia.
Qed.

Theorem wp_UInt64Get_unchanged stk E s q (x: u64) vs :
  take 8 vs = u64_le_bytes x →
  {{{ own_slice_small s byteT q vs }}}
    UInt64Get (slice_val s) @ stk; E
  {{{ RET #x; own_slice_small s byteT q vs }}}.
Proof.
  iIntros (Htake8 Φ) "Hs HΦ".
  rewrite -(take_drop 8 vs).
  wp_apply (wp_UInt64Get with "[$Hs]").
  { iPureIntro.
    rewrite Htake8.
    rewrite take_app_le; len; eauto. }
  iIntros "Hs".
  rewrite -Htake8.
  iApply "HΦ".
  iExactEq "Hs".
  f_equal.
  f_equal.
  rewrite drop_app_le.
  { rewrite [drop _ (take _ _)]drop_ge //; len. }
  len.
  apply (f_equal length) in Htake8.
  autorewrite with len in Htake8.
  rewrite Htake8.
  auto.
Qed.

Theorem wp_UInt64Get' stk E s q (x: u64) :
  {{{ s.(Slice.ptr) ↦∗[byteT]{q} u64_le_bytes x ∗ ⌜uint.Z s.(Slice.sz) >= 8⌝ }}}
    UInt64Get (slice_val s) @ stk; E
  {{{ RET #x; s.(Slice.ptr) ↦∗[byteT]{q} u64_le_bytes x }}}.
Proof.
  iIntros (Φ) "[Ha %] HΦ".
  wp_call.
  wp_call.
  wp_apply (wp_DecodeUInt64 with "Ha").
  iApply "HΦ".
Qed.

Theorem wp_UInt32Get' stk E s q (x: u32) :
  {{{ s.(Slice.ptr) ↦∗[byteT]{q} u32_le_bytes x ∗ ⌜uint.Z s.(Slice.sz) >= 4⌝ }}}
    UInt32Get (slice_val s) @ stk; E
  {{{ RET #x; s.(Slice.ptr) ↦∗[byteT]{q} u32_le_bytes x }}}.
Proof.
  iIntros (Φ) "[Ha %] HΦ".
  wp_call.
  wp_call.
  wp_apply (wp_DecodeUInt32 with "Ha").
  iApply "HΦ".
Qed.

Theorem wp_UInt32Get_unchanged stk E s q (x: u32) vs :
  take 4 vs = u32_le_bytes x →
  {{{ own_slice_small s byteT q vs }}}
    UInt32Get (slice_val s) @ stk; E
  {{{ RET #x; own_slice_small s byteT q vs }}}.
Proof.
  iIntros (Htake Φ) "Hs HΦ".
  rewrite /own_slice_small.
  iDestruct "Hs" as "[Hptr %]".
  rewrite -(take_drop 4 vs).
  iDestruct (array_app with "Hptr") as "[Hptr1 Hptr2]".
  wp_apply (wp_UInt32Get' with "[Hptr1]").
  { rewrite Htake; iFrame.
    iPureIntro.
    apply (f_equal length) in Htake.
    move: Htake.
    rewrite u32_le_bytes_length; len. }
  iIntros "Hptr1".
  rewrite -Htake.
  iDestruct (array_app with "[$Hptr1 $Hptr2]") as "Hptr".
  rewrite take_drop.
  iApply "HΦ".
  by iFrame "∗ %".
Qed.

End heap.

#[global]
Hint Rewrite @u64_le_bytes_length : len.
#[global]
Hint Rewrite @u32_le_bytes_length : len.

Ltac Zify.zify_post_hook ::= idtac.
