From New.generatedproof Require Import encoding.binary.
From New.proof Require Import sync slices math io errors.
From Perennial.Helpers.Word Require Import LittleEndian.
From coqutil.Z Require Import bitblast prove_Zeq_bitwise.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : binary.Assumptions}.
Collection W := sem + package_sem.

Local Definition is_init : iProp Σ :=
  global_addr binary.LittleEndian ↦□ binary.littleEndian.mk.
#[global] Instance : IsPkgInit (iProp Σ) binary := define_is_pkg_init is_init%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) binary := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop binary get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    binary.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init binary }}}.
Proof using W.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply wp_GlobalAlloc as "?".
  wp_apply wp_GlobalAlloc as "Hlit". iPersist "Hlit".
  wp_apply wp_GlobalAlloc as "?".
  wp_apply (sync.wp_initialize' with "[$Hown]") as "(Hown & #?)"; first naive_solver.
  wp_apply (slices.wp_initialize' with "[$Hown]") as "(Hown & #?)"; first naive_solver.
  wp_apply (math.wp_initialize' with "[$Hown]") as "(Hown & #?)"; first naive_solver.
  wp_apply (io.wp_initialize' with "[$Hown]") as "(Hown & #?)"; first naive_solver.
  wp_apply (errors.wp_initialize' with "[$Hown]") as "(Hown & #?)"; first naive_solver.
  wp_apply wp_New as "% _". wp_apply wp_New as "% _".
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#".
Qed.

Lemma word_wrap_wrap `{word1: Interface.word width1} `{word2: Interface.word width2}
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

Hint Rewrite word.unsigned_of_Z : word.
Hint Rewrite word.unsigned_sru : word.

(* TODO: should prob go in shared Word / byte helpers. *)
Lemma word64_byte_extract (x:u64) k :
  0 <= k < 8 ->
  word.of_Z (uint.Z x ≫ (k*8)) = W8 (uint.Z (word.sru x (W64 (k*8)))).
Proof.
  intros.
  apply word.unsigned_inj.
  unfold W8.
  autorewrite with word.
  rewrite word.unsigned_sru;
    rewrite word.unsigned_of_Z.
  { rewrite word_wrap_wrap; last lia.
    rewrite [word.wrap (k * _)]wrap_small; last lia.
    reflexivity.
  }
  rewrite wrap_small; lia.
Qed.

Lemma w8_land_ones (x:w8) : Z.land (uint.Z x) (Z.ones 8) = uint.Z x.
Proof. rewrite (Z.land_ones (uint.Z x) 8); [ apply Z.mod_small; word | lia ]. Qed.

Lemma wp_littleEndian_Uint64 (le : binary.littleEndian.t) b (bs : list w8) rem dq :
  length bs = 8%nat →
  {{{ b ↦*{dq} (bs ++ rem) }}}
    le @! binary.littleEndian @! "Uint64" #b
  {{{ RET #(le_to_u64 bs); b ↦*{dq} (bs ++ rem) }}}.
Proof using W.
  rewrite le_to_u64_unseal /le_to_u64_def.
  iIntros (Hlen_bs).
  wp_start as "Hb".
  iDestruct (own_slice_len with "Hb") as %[Hlen_b ?].
  rewrite app_length Hlen_bs in Hlen_b.
  wp_auto.
  list_elem bs 7 as b7.
  do 9 (destruct bs as [|? bs]; try done).

  repeat (rewrite -> decide_True; last word;
          wp_apply (wp_load_slice_index with "[$Hb]") as "Hb"; [len| | ];
          [iPureIntro; rewrite lookup_app_l //; word | ]).

  wp_end.
  replace (sint.nat (W64 0)) with (0%nat) by word.
  replace (sint.nat (W64 1)) with (1%nat) by word.
  replace (sint.nat (W64 2)) with (2%nat) by word.
  replace (sint.nat (W64 3)) with (3%nat) by word.
  replace (sint.nat (W64 4)) with (4%nat) by word.
  replace (sint.nat (W64 5)) with (5%nat) by word.
  replace (sint.nat (W64 6)) with (6%nat) by word.
  replace (sint.nat (W64 7)) with (7%nat) by word.
  repeat (destruct bs; try done).
  f_equal.
  assert (b7 = w6) as -> by (simpl in Hb7_lookup; congruence).
  apply word.unsigned_inj.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; [ | apply combine_bound ].
  cbn [length HList.tuple.of_list].
  rewrite !combine_unfold.
  cbn [LittleEndian.combine].
  change (LittleEndian.combine 0 ()) with 0%Z.
  rewrite Z.shiftl_0_l Z.lor_0_r.
  rewrite !word.unsigned_or.
  rewrite !word.unsigned_slu; [ | word | word | word | word | word | word | word ].
  replace (uint.Z (W64 8)) with 8 by word.
  replace (uint.Z (W64 16)) with 16 by word.
  replace (uint.Z (W64 24)) with 24 by word.
  replace (uint.Z (W64 32)) with 32 by word.
  replace (uint.Z (W64 40)) with 40 by word.
  replace (uint.Z (W64 48)) with 48 by word.
  replace (uint.Z (W64 56)) with 56 by word.
  rewrite !word.unsigned_of_Z.
  unfold word.wrap.
  rewrite <-!Z.land_ones; try lia.
  rewrite <-(w8_land_ones w).
  rewrite <-(w8_land_ones w0).
  rewrite <-(w8_land_ones w1).
  rewrite <-(w8_land_ones w2).
  rewrite <-(w8_land_ones w3).
  rewrite <-(w8_land_ones w4).
  rewrite <-(w8_land_ones w5).
  rewrite <-(w8_land_ones w6).
  prove_Zeq_bitwise.
Qed.

Lemma wp_littleEndian_PutUint64 (le : binary.littleEndian.t) b space rem v :
  length space = 8%nat →
  {{{ b ↦* (space ++ rem) }}}
    le @! binary.littleEndian @! "PutUint64" #b #v
  {{{ RET #(); b ↦* (u64_le v ++ rem) }}}.
Proof using W.
  rewrite u64_le_unseal /u64_le_def.
  iIntros (Hlen_space).
  wp_start as "Hb".
  iDestruct (own_slice_len with "Hb") as %[Hlen_b ?].
  rewrite app_length Hlen_space in Hlen_b.
  wp_auto.
  rewrite -> decide_True; last word.
  list_elem space 7 as canary.

  wp_apply (wp_load_slice_index with "[$Hb]") as "Hb"; [len| | ].
  { iPureIntro. rewrite lookup_app_l //. word. }

  (* FIXME: [rewrite decide_True] is slow *)
  repeat (rewrite -> decide_True; last word; wp_auto;
          wp_apply (wp_store_slice_index with "[$Hb]") as "Hb"; [len|]).

  wp_end.
  replace (sint.nat (W64 0)) with (0%nat) by word.
  replace (sint.nat (W64 1)) with (1%nat) by word.
  replace (sint.nat (W64 2)) with (2%nat) by word.
  replace (sint.nat (W64 3)) with (3%nat) by word.
  replace (sint.nat (W64 4)) with (4%nat) by word.
  replace (sint.nat (W64 5)) with (5%nat) by word.
  replace (sint.nat (W64 6)) with (6%nat) by word.
  replace (sint.nat (W64 7)) with (7%nat) by word.
  repeat (destruct space; try done).
  simpl. iExactEq "Hb". f_equal.
  rewrite (word64_byte_extract _ 1) //.
  rewrite (word64_byte_extract _ 2) //.
  rewrite (word64_byte_extract _ 3) //.
  rewrite (word64_byte_extract _ 4) //.
  rewrite (word64_byte_extract _ 5) //.
  rewrite (word64_byte_extract _ 6) //.
  rewrite (word64_byte_extract _ 7) //.
Qed.

Lemma wp_LittleEndian_PutUint64 b space rem v :
  length space = 8%nat →
  {{{ is_pkg_init binary ∗ b ↦* (space ++ rem) }}}
    (global_addr binary.LittleEndian) @! (go.PointerType binary.littleEndian) @! "PutUint64" #b #v
  {{{ RET #(); b ↦* (u64_le v ++ rem) }}}.
Proof using W.
  intros ?. wp_start.
  iDestruct (is_pkg_init_access with "[$]") as "H".
  simpl. iNamed "H". wp_auto.
  by wp_apply (wp_littleEndian_PutUint64 with "[$]").
Qed.

Lemma wp_LittleEndian_Uint64 b bs dq rem :
  length bs = 8%nat →
  {{{ is_pkg_init binary ∗ b ↦*{dq} (bs ++ rem) }}}
    (global_addr binary.LittleEndian) @! (go.PointerType binary.littleEndian) @! "Uint64" #b
  {{{ RET #(le_to_u64 bs); b ↦*{dq} (bs ++ rem) }}}.
Proof using W.
  intros ?. wp_start.
  iDestruct (is_pkg_init_access with "[$]") as "H".
  simpl. iNamed "H". wp_auto.
  by wp_apply (wp_littleEndian_Uint64 with "[$]").
Qed.

(** 32-bit little-endian, mirroring the 64-bit lemmas above. *)

Lemma word32_byte_extract (x:u32) k :
  0 <= k < 4 ->
  word.of_Z (uint.Z x ≫ (k*8)) = W8 (uint.Z (word.sru x (W32 (k*8)))).
Proof.
  intros.
  apply word.unsigned_inj.
  unfold W8.
  autorewrite with word.
  rewrite word.unsigned_sru;
    rewrite word.unsigned_of_Z.
  { rewrite word_wrap_wrap; last lia.
    rewrite [word.wrap (k * _)]wrap_small; last lia.
    reflexivity.
  }
  rewrite wrap_small; lia.
Qed.

Lemma wp_littleEndian_PutUint32 (le : binary.littleEndian.t) b space rem v :
  length space = 4%nat →
  {{{ b ↦* (space ++ rem) }}}
    le @! binary.littleEndian @! "PutUint32" #b #v
  {{{ RET #(); b ↦* (u32_le v ++ rem) }}}.
Proof using W.
  rewrite u32_le_unseal /u32_le_def.
  iIntros (Hlen_space).
  wp_start as "Hb".
  iDestruct (own_slice_len with "Hb") as %[Hlen_b ?].
  rewrite app_length Hlen_space in Hlen_b.
  wp_auto.
  rewrite -> decide_True; last word.
  list_elem space 3 as canary.

  wp_apply (wp_load_slice_index with "[$Hb]") as "Hb"; [len| | ].
  { iPureIntro. rewrite lookup_app_l //. word. }

  repeat (rewrite -> decide_True; last word; wp_auto;
          wp_apply (wp_store_slice_index with "[$Hb]") as "Hb"; [len|]).

  wp_end.
  replace (sint.nat (W64 0)) with (0%nat) by word.
  replace (sint.nat (W64 1)) with (1%nat) by word.
  replace (sint.nat (W64 2)) with (2%nat) by word.
  replace (sint.nat (W64 3)) with (3%nat) by word.
  repeat (destruct space; try done).
  simpl. iExactEq "Hb". f_equal.
  rewrite (word32_byte_extract _ 1) //.
  rewrite (word32_byte_extract _ 2) //.
  rewrite (word32_byte_extract _ 3) //.
Qed.

Lemma wp_LittleEndian_PutUint32 b space rem v :
  length space = 4%nat →
  {{{ is_pkg_init binary ∗ b ↦* (space ++ rem) }}}
    (global_addr binary.LittleEndian) @! (go.PointerType binary.littleEndian) @! "PutUint32" #b #v
  {{{ RET #(); b ↦* (u32_le v ++ rem) }}}.
Proof using W.
  intros ?. wp_start.
  iDestruct (is_pkg_init_access with "[$]") as "H".
  simpl. iNamed "H". wp_auto.
  by wp_apply (wp_littleEndian_PutUint32 with "[$]").
Qed.

Lemma wp_littleEndian_Uint32 (le : binary.littleEndian.t) b (bs : list w8) rem dq :
  length bs = 4%nat →
  {{{ b ↦*{dq} (bs ++ rem) }}}
    le @! binary.littleEndian @! "Uint32" #b
  {{{ RET #(le_to_u32 bs); b ↦*{dq} (bs ++ rem) }}}.
Proof using W.
  rewrite le_to_u32_unseal /le_to_u32_def.
  iIntros (Hlen_bs).
  wp_start as "Hb".
  iDestruct (own_slice_len with "Hb") as %[Hlen_b ?].
  rewrite app_length Hlen_bs in Hlen_b.
  wp_auto.
  list_elem bs 3 as b3.
  do 5 (destruct bs as [|? bs]; try done).

  repeat (rewrite -> decide_True; last word;
          wp_apply (wp_load_slice_index with "[$Hb]") as "Hb"; [len| | ];
          [iPureIntro; rewrite lookup_app_l //; word | ]).

  wp_end.
  replace (sint.nat (W64 0)) with (0%nat) by word.
  replace (sint.nat (W64 1)) with (1%nat) by word.
  replace (sint.nat (W64 2)) with (2%nat) by word.
  replace (sint.nat (W64 3)) with (3%nat) by word.
  repeat (destruct bs; try done).
  f_equal.
  assert (b3 = w2) as -> by (simpl in Hb3_lookup; congruence).
  apply word.unsigned_inj.
  rewrite word.unsigned_of_Z.
  rewrite wrap_small; [ | apply combine_bound ].
  cbn [length HList.tuple.of_list].
  rewrite !combine_unfold.
  cbn [LittleEndian.combine].
  change (LittleEndian.combine 0 ()) with 0%Z.
  rewrite Z.shiftl_0_l Z.lor_0_r.
  rewrite !word.unsigned_or.
  rewrite !word.unsigned_slu; [ | word | word | word ].
  replace (uint.Z (W32 8)) with 8 by word.
  replace (uint.Z (W32 16)) with 16 by word.
  replace (uint.Z (W32 24)) with 24 by word.
  rewrite !word.unsigned_of_Z.
  unfold word.wrap.
  rewrite <-!Z.land_ones; try lia.
  rewrite <-(w8_land_ones w).
  rewrite <-(w8_land_ones w0).
  rewrite <-(w8_land_ones w1).
  rewrite <-(w8_land_ones w2).
  prove_Zeq_bitwise.
Qed.

Lemma wp_LittleEndian_Uint32 b bs dq rem :
  length bs = 4%nat →
  {{{ is_pkg_init binary ∗ b ↦*{dq} (bs ++ rem) }}}
    (global_addr binary.LittleEndian) @! (go.PointerType binary.littleEndian) @! "Uint32" #b
  {{{ RET #(le_to_u32 bs); b ↦*{dq} (bs ++ rem) }}}.
Proof using W.
  intros ?. wp_start.
  iDestruct (is_pkg_init_access with "[$]") as "H".
  simpl. iNamed "H". wp_auto.
  by wp_apply (wp_littleEndian_Uint32 with "[$]").
Qed.

End wps.
