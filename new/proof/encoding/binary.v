From New.generatedproof Require Import encoding.binary.
From New.proof Require Import sync slices math io errors.

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
  (* TODO now: finish byte-level reasoning for Uint64 decode. Here's the goal:
1 goal (ID 122066)

  ext : ffi_syntax
  ffi : ffi_model
  ffi_interp0 : ffi_interp ffi
  Σ : gFunctors
  hG : heapGS Σ
  ffi_semantics0 : ffi_semantics ext ffi
  sem : go.Semantics
  package_sem : binary.Assumptions
  le : binary.littleEndian.t
  b : slice.t
  w, w0, w1, w2, w3, w4, w5, w6 : w8
  rem : list w8
  dq : dfrac
  Hlen_bs : length [w; w0; w1; w2; w3; w4; w5; w6] = 8%nat
  Φ : val → iPropI Σ
  H : 0 ≤ sint.Z b.(slice.len)
  Hlen_b : (8 + length rem)%nat = sint.nat b.(slice.len)
  b_ptr : loc
  b7 : w8
  Hb7_lookup : [w; w0; w1; w2; w3; w4; w5; w6] !! Z.to_nat 7 = Some b7
  ============================
  w64_word_instance.(word.of_Z)
    (LittleEndian.combine (length [w; w0; w1; w2; w3; w4; w5; w6])
       (HList.tuple.of_list [w; w0; w1; w2; w3; w4; w5; w6])) =
  w64_word_instance.(word.or)
    (w64_word_instance.(word.or)
       (w64_word_instance.(word.or)
          (w64_word_instance.(word.or)
             (w64_word_instance.(word.or)
                (w64_word_instance.(word.or)
                   (w64_word_instance.(word.or) (W64 (uint.Z w))
                      (w64_word_instance.(word.slu) (W64 (uint.Z w0)) (W64 8)))
                   (w64_word_instance.(word.slu) (W64 (uint.Z w1)) (W64 16)))
                (w64_word_instance.(word.slu) (W64 (uint.Z w2)) (W64 24)))
             (w64_word_instance.(word.slu) (W64 (uint.Z w3)) (W64 32)))
          (w64_word_instance.(word.slu) (W64 (uint.Z w4)) (W64 40)))
       (w64_word_instance.(word.slu) (W64 (uint.Z w5)) (W64 48)))
    (w64_word_instance.(word.slu) (W64 (uint.Z b7)) (W64 56))
 *)
Admitted.

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

End wps.
