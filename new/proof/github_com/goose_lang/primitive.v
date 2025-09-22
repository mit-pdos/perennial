From New.proof Require Import proof_prelude.
Require Import New.code.github_com.goose_lang.primitive.
Require Import New.generatedproof.github_com.goose_lang.primitive.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit primitive := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf primitive := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop primitive get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init ∗ is_go_context ∗ □ is_pkg_defined primitive }}}
    primitive.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init primitive }}}.
Proof.
  intros Hinit. wp_start as "(Hown & #? & #Hdef)".
  wp_call. wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.

  wp_call. iEval (rewrite is_pkg_init_unfold /=).
  by iFrame "∗#".
Qed.

Lemma wp_Assume (cond : bool) :
  {{{ is_pkg_init primitive }}}
    @! primitive.Assume #cond
  {{{ RET #(); ⌜ cond = true ⌝ }}}
.
Proof.
  wp_start as "#Hdef".
  destruct cond; wp_auto.
  - iApply ("HΦ" with "[//]").
  - iLöb as "IH". wp_auto.
    wp_apply ("IH" with "[$]").
Qed.

Lemma wp_RandomUint64 :
  {{{ is_pkg_init primitive }}}
    @! primitive.RandomUint64 #()
  {{{ (x: w64), RET #x; True }}}
.
Proof.
  wp_start as "_".
  wp_apply wp_ArbitraryInt.
  iIntros (x).
  iApply "HΦ".
  done.
Qed.

Lemma wp_AssumeNoStringOverflow (s: byte_string) :
  {{{ is_pkg_init primitive }}}
    @! primitive.AssumeNoStringOverflow #s
  {{{ RET #(); ⌜Z.of_nat (length s) < 2^64⌝ }}}.
Proof.
  wp_start as "_".
  wp_call.
  wp_if_destruct.
  - iApply "HΦ". done.
  - iLöb as "IH".
    wp_pures.
    iApply "IH".
    iApply "HΦ".
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

Lemma wp_UInt64Put sl_b space rem v :
  length space = 8%nat →
  {{{ is_pkg_init primitive ∗ sl_b ↦* (space ++ rem) }}}
    @! primitive.UInt64Put #sl_b #v
  {{{ RET #(); sl_b ↦* (u64_le v ++ rem) }}}.
Proof.
  rewrite u64_le_unseal /u64_le_def.
  iIntros (Hlen_space).
  wp_start as "Hsl_b".
  iDestruct (own_slice_len with "Hsl_b") as %[Hlen_b ?].
  rewrite app_length Hlen_space in Hlen_b.
  repeat (
    wp_pure; [word|];
    wp_apply (wp_store_slice_elem with "[$Hsl_b]") as "Hsl_b"; [len|]).

  iApply "HΦ".
  replace (sint.nat (W64 0)) with (0%nat) by word.
  replace (sint.nat (W64 1)) with (1%nat) by word.
  replace (sint.nat (W64 2)) with (2%nat) by word.
  replace (sint.nat (W64 3)) with (3%nat) by word.
  replace (sint.nat (W64 4)) with (4%nat) by word.
  replace (sint.nat (W64 5)) with (5%nat) by word.
  replace (sint.nat (W64 6)) with (6%nat) by word.
  replace (sint.nat (W64 7)) with (7%nat) by word.
  repeat (destruct space; try done).
  simpl.
  rewrite -!word64_byte_extract; [|lia..].
  iFrame.
Qed.

End wps.
