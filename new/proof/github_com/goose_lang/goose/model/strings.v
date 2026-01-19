From New.proof Require Import proof_prelude.
Require Import New.code.github_com.goose_lang.goose.model.strings.
Require Import New.generatedproof.github_com.goose_lang.goose.model.strings.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.StringSemantics}.

Local Set Default Proof Using "All".

Lemma wp_string_len (s : go_string) `[!t ↓u go.string] :
  {{{ True }}}
    (#(functions go.len [t]) #s)
  {{{ RET #(W64 (length s)); ⌜ length s < 2^63 ⌝ }}}.
Proof.
  wp_start. wp_if_destruct.
  - iApply "HΦ". word.
  - wp_apply wp_AngelicExit.
Qed.

Lemma wp_StringToByteSlice (s : go_string) :
  {{{ True }}}
    @! strings.StringToByteSlice #s
  {{{ sl, RET #sl; sl ↦* s }}}.
Proof.
  wp_start. wp_auto.
  iAssert (
      ∃ (i : w64) a,
        "i" ∷ i_ptr ↦ i ∗
        "a" ∷ a_ptr ↦ a ∗
        "Ha" ∷ a ↦* (take (sint.nat i) s) ∗
        "Ha_cap" ∷ own_slice_cap w8 a (DfracOwn 1) ∗
        "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ (sint.nat (W64 $ length s)) ⌝
    )%I with "[a i]" as "H".
  { iFrame. iDestruct own_slice_nil as "$".
    iDestruct own_slice_cap_nil as "$". word. }
  wp_for "H".
  wp_apply wp_string_len as "%Hoverflow".
  wp_if_destruct.
  - list_elem s (sint.nat i) as c.
    rewrite Hc_lookup. wp_auto. rewrite go.array_index_ref_0.
    iDestruct (slice_array with "tmp") as "Hsl".
    { simpl. len. }
    wp_apply (wp_slice_append with "[$Ha $Ha_cap $Hsl]").
    iIntros "* (Ha & Ha_cap & _)". wp_auto.
    wp_for_post.
    iFrame. iSplitL; last word.
    iApply to_named. iExactEq "Ha". f_equal.
    simpl. replace (sint.nat 0) with O by word.
    simpl. rewrite -take_S_r; last done.
    f_equal. word.
  - iApply "HΦ". rewrite take_ge; last len. iFrame.
Qed.

Lemma wp_ByteSliceToString sl (s : list w8) dq :
  {{{ sl ↦*{dq} s }}}
    @! strings.ByteSliceToString #sl
  {{{ RET #s; sl ↦*{dq} s }}}.
Proof.
  wp_start as "Hsl". wp_auto.
  iDestruct (own_slice_len with "[$]") as %Hlen.
  iAssert (
      ∃ (i : w64) (c : w8),
        "i" ∷ i_ptr ↦ i ∗
        "c" ∷ c_ptr ↦ c ∗
        "s" ∷ s_ptr ↦ (take (sint.nat i) s) ∗
        "%Hi" ∷ ⌜ 0 ≤ sint.Z i ≤ length s ⌝
    )%I with "[s c i]" as "H".
  { iFrame. word. }
  wp_for "H".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem s (sint.nat i) as c'.
    wp_auto. wp_apply (wp_load_slice_index with "[$Hsl]").
    { word. }
    { done. }
    iIntros "Hsl".
    wp_auto.
    wp_for_post.
    iFrame. iSplitL; last word.
    iApply to_named. iExactEq "s". f_equal.
    rewrite -take_S_r; last done. f_equal. word.
  - rewrite take_ge; last word. iApply "HΦ". iFrame.
Qed.

End wps.
