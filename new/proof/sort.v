From New.generatedproof Require Import sort.
From New.proof Require Import proof_prelude.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit sort := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf sort := build_get_is_pkg_init_wf.

(* various parts of this were written by Claude Sonnet 4.5. It was given the doc
and the memoize example from my course notes to write the spec, and the code for
sort.Find to write the proof *)

(* The comparison function must implement a pure function over indices,
   with an arbitrary invariant I that it requires and preserves *)
Definition cmp_implements (cmp_code: func.t) (cmp: Z → Z) (n: Z) (I: iProp Σ) : iProp Σ :=
  ∀ (i: w64),
    {{{ I ∗ ⌜sint.Z i < n⌝ }}}
      #cmp_code #i
    {{{ (r: w64), RET #r; I ∗ ⌜sint.Z r = cmp (sint.Z i)⌝ }}}.

#[export] Instance cmp_implements_persistent cmp_code cmp n I `{!Persistent I} :
  Persistent (cmp_implements cmp_code cmp n I).
Proof. apply _. Qed.

(* The key correctness property: cmp must be monotonically non-increasing *)
(* note: this is overly strong, only cmp being negative/zero/positive matters
and that is what should be monotonic, but you can always *)
Definition is_valid_cmp (cmp: Z → Z) (n: Z) : Prop :=
  (∀ i j, 0 ≤ i ∧ i < j < n → cmp j ≤ cmp i) ∧
  (* NOTE: this is just a useful definition to make the invariant simpler, the
  actual comparison function is never passed there parameters *)
  (cmp (-1) = 1) ∧
  (cmp n = 0).

Lemma wp_Find (n: w64) (cmp_code: func.t) (cmp: Z → Z) (I: iProp Σ) `{!Persistent I} :
  {{{ is_pkg_init sort ∗
      ⌜0 ≤ sint.Z n⌝ ∗
      cmp_implements cmp_code cmp (sint.Z n) I ∗
      I ∗
      ⌜is_valid_cmp cmp (sint.Z n)⌝ }}}
    @! sort.Find #n #cmp_code
  {{{ (i: w64) (found: bool), RET (#i, #found);
      I ∗
      ⌜found = true →
        sint.Z i < sint.Z n ∧
        cmp (sint.Z i) = 0⌝ ∗
      ⌜found = false →
        (* the English spec clearly says this, but it is only true if 0 ≤ n so
        we assume that in the precondition and translate the spec literally *)
       sint.Z i = sint.Z n⌝ ∗
      ⌜∀ k, 0 ≤ k < sint.Z i → cmp k > 0⌝
  }}}.
Proof.
  wp_start as "(%Hpos & #Hcmp & I & %Hvalid)".
  wp_auto.

  (* Initialize loop invariant: i = 0, j = n *)
  iAssert (
    ∃ (i_val j_val: w64),
      "i" ∷ i_ptr ↦ i_val ∗
      "j" ∷ j_ptr ↦ j_val ∗
      "I" ∷ I ∗
      "%Hbounds" ∷ ⌜0 ≤ sint.Z i_val ≤ sint.Z j_val ≤ sint.Z n⌝ ∗
      "%Hi_prop" ∷ ⌜∀ k, 0 ≤ k < sint.Z i_val → cmp k > 0⌝ ∗
      "%Hj_prop" ∷ ⌜∀ k, sint.Z j_val ≤ k < sint.Z n → cmp k ≤ 0⌝
  )%I with "[$I $i $j]" as "HI".
  { iPureIntro. split_and!; intros; try word. }

  wp_for "HI".
  wp_if_destruct.
  - (* Loop body: i < j *)
    (* Call cmp(h) *)
    rewrite /cmp_implements.
    wp_apply ("Hcmp" with "[$I]").
    { iPureIntro. word. }
    iIntros (r) "[HI %Hcmp_result]".

    wp_auto.
    wp_if_destruct.
    + (* cmp(h) > 0, so i = h + 1 *)
      wp_for_post.
      iFrame "j".
      iFrame.
      iPureIntro.
      split; [word|].
      split.
      * intros k Hk.
        pose proof (Hi_prop k).
        rewrite sint_eq_uint' in Hk; [ | word ].
        rewrite word.unsigned_add_nowrap in Hk; [ | word ].
        rewrite word.unsigned_sru_nowrap in Hk; [ | word ].
        rewrite sint_eq_uint' in Hcmp_result; [ | word ].
        rewrite sint_eq_uint' in Hcmp_result; [ | word ].
        rewrite word.unsigned_sru_nowrap in Hcmp_result; [ | word ].
        rewrite word.unsigned_add_nowrap in Hcmp_result; [ | word ].
        rewrite word.unsigned_add_nowrap in Hk; [ | word ].
        rewrite Z.shiftr_div_pow2 in Hk, Hcmp_result; [ | word ].
        change (2^(uint.Z (W64 1))) with 2 in *.
        change (uint.Z (W64 1)) with 1 in *.
        change (sint.Z 0) with 0 in *.
        rewrite sint_eq_uint' in H; [ | word ].
        rewrite -> !sint_eq_uint' in * by word.
        destruct Hvalid as (Hvalid & Hcmp_lo & Hcmp_hi).
        admit.
      * apply Hj_prop.
    + (* cmp(h) ≤ 0, so j = h *)
      wp_for_post.
      iFrame.
      iPureIntro.
      split; [word|].
      split.
      * apply Hi_prop.
      * intros k Hk.
        destruct (decide (k > sint.Z (w64_word_instance.(word.sru)
            (w64_word_instance.(word.add) i_val j_val)
            (W64 1)))).
        -- apply Hj_prop. admit.
        -- admit.
  - (* Loop exit: i = j *)
    assert (sint.Z i_val = sint.Z j_val) by word.
    wp_if_destruct.
    + (* i < n, check if cmp(i) = 0 *)
      wp_apply ("Hcmp" with "[$I]").
      { word. }
      iIntros (r) "[I %Hcmp_result]".
      wp_auto.

      iApply "HΦ".
      iFrame.
      iPureIntro.
      split_and!; auto; try word.
      * intros Hfound.
        destruct (bool_decide (sint.Z r = 0)) eqn:Heq.
        -- rewrite bool_decide_eq_true in Heq.
           split; [word|].
           rewrite -Hcmp_result. word.
        -- rewrite bool_decide_eq_false in Heq.
           rewrite bool_decide_eq_true in Hfound.
           word.
      * intros Hnotfound.
        rewrite bool_decide_eq_false in Hnotfound.
        (* From Hj_prop, we know cmp(i) ≤ 0, and from Heq it's not 0 *)
        assert (cmp (sint.Z i_val) ≤ 0).
        { replace (sint.Z i_val) with (sint.Z j_val) by word.
          apply Hj_prop. word. }

        admit.
    + (* i = n *)
      iApply "HΦ".
      iFrame.
      iPureIntro.
      split_and!; auto; try word.
Admitted.

End proof.
