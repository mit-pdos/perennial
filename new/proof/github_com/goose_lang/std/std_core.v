From New.proof Require Import proof_prelude.
From New.code.github_com.goose_lang Require Export std_core.
From New.generatedproof.github_com.goose_lang Require Export std_core.
From New.proof Require Import github_com.goose_lang.primitive.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.
Context {package_sem : std_core.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) std_core := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) std_core := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop std_core get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    std_core.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init std_core }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?); done. }
  iIntros "Hown". wp_auto.
  wp_apply (primitive.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#". done.
Qed.

Lemma wp_SumNoOverflow (x y : u64) :
  {{{ is_pkg_init std_core }}}
    @! std_core.SumNoOverflow #x #y
  {{{ RET #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)); True }}}.
Proof.
  wp_start as "_". wp_auto.
  iSpecialize ("HΦ" with "[$]").
  iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  pose proof (sum_overflow_check x y).
  word.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) :
  {{{ is_pkg_init std_core }}}
    @! std_core.SumAssumeNoOverflow #x #y
  {{{ RET #(word.add x y); ⌜uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z⌝ }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply wp_SumNoOverflow.
  wp_apply wp_Assume as "%Hassume".
  rewrite bool_decide_eq_true in Hassume.
  iApply "HΦ". iPureIntro. done.
Qed.

Lemma wp_MulNoOverflow (x y : u64) :
  {{{ is_pkg_init std_core }}}
    @! std_core.MulNoOverflow #x #y
  {{{ RET #(bool_decide (uint.Z (word.mul x y) = (uint.Z x * uint.Z y)%Z)); True }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_if_destruct.
  { rewrite -> bool_decide_eq_true_2 by word.
    iApply "HΦ"; auto. }
  wp_if_destruct.
  { rewrite -> bool_decide_eq_true_2 by word.
    iApply "HΦ"; auto. }
  iSpecialize ("HΦ" with "[$]").
  iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  pose proof (mul_overflow_check_correct x y ltac:(word) ltac:(word)).
  word.
Qed.

Lemma wp_MulAssumeNoOverflow (x y : u64) :
  {{{ is_pkg_init std_core }}}
    @! std_core.MulAssumeNoOverflow #x #y
  {{{ RET #(word.mul x y); ⌜uint.Z (word.mul x y) = (uint.Z x * uint.Z y)%Z⌝ }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply wp_MulNoOverflow.
  wp_apply wp_Assume as "%Hassume".
  rewrite bool_decide_eq_true in Hassume.
  iApply "HΦ". iPureIntro. done.
Qed.

#[local] Unset Printing Projections.

Lemma wp_Shuffle s (xs: list w64) :
  {{{ is_pkg_init std_core ∗ s ↦* xs }}}
    @! std_core.Shuffle #s
  {{{ xs', RET #(); ⌜Permutation xs xs'⌝ ∗
                      s ↦* xs' }}}.
Proof.
  wp_start as "Hs".
  wp_auto.
  iPersist "xs".
  iDestruct (own_slice_len with "Hs") as %Hlen.
  iDestruct (own_slice_wf with "Hs") as %Hwf.
  destruct (bool_decide_reflect (slice.len s = W64 0)); wp_auto.
  {
    assert (xs = []); subst .
    { destruct xs; auto; simpl in *; word.  }
    iApply "HΦ".
    iFrame. auto.
  }
  iAssert (∃ (i: w64) (xs': list w64),
              "i" ∷ i_ptr ↦ i ∗
              "%HI" ∷ ⌜0 ≤ sint.Z i < sint.Z (slice.len s)⌝ ∗
              "Hs" ∷ s ↦* xs' ∗
              "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝
          )%I with "[$i $Hs]" as "IH".
  { iPureIntro.
    split.
    - word.
    - auto. }
  wp_for "IH".
  pose proof (Permutation_length Hperm) as Hleneq.
  change (uint.Z (W64 0)) with 0.
  destruct (bool_decide_reflect (0 < uint.Z i)).
  - wp_auto.
    wp_apply wp_RandomUint64.
    iIntros (x) "_".
    wp_auto.
    list_elem xs' (sint.Z i) as x_i.
    rewrite -> decide_True; last word. wp_auto.
    wp_apply (wp_load_slice_index with "[$Hs]") as "Hs"; [ word | eauto | ].
    rewrite -> decide_True; last word. wp_auto.

    list_elem xs' (sint.nat (word.modu x (word.add i (W64 1)))) as x_i'.
    wp_apply (wp_load_slice_index with "[$Hs]") as "Hs"; [ word | eauto | ].
    rewrite -> decide_True; last word. wp_auto.
    wp_apply (wp_store_slice_index with "[$Hs]") as "Hs".
    { word. }
    rewrite -> decide_True; last word. wp_auto.
    wp_apply (wp_store_slice_index with "[$Hs]") as "Hs"; [ len | ].
    wp_for_post.
    iFrame.
    iPureIntro.
    split; [ word | ].
    trans xs'; auto.
    erewrite Permutation_insert_swap; eauto.
  - wp_auto.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    auto.
Qed.

Lemma seqZ_plus_1 n m :
  0 ≤ m →
  seqZ n (m + 1) = seqZ n m ++ [n + m].
Proof.
  intros.
  rewrite seqZ_app; try lia.
  reflexivity.
Qed.

Lemma wp_Permutation (n: w64) :
  {{{ is_pkg_init std_core ∗ ⌜0 ≤ sint.Z n⌝ }}}
    @! std_core.Permutation #n
  {{{ xs s, RET #s;
      ⌜xs ≡ₚ (W64 <$> seqZ 0 (sint.Z n))⌝ ∗
      s ↦* xs
  }}}.
Proof.
  wp_start as "%Hnz".
  wp_auto.
  wp_apply wp_slice_make2.
  { word. }
  iIntros (s) "[Hs _]".
  wp_auto.
  iDestruct (own_slice_len with "Hs") as "%Hlen".
  autorewrite with len in Hlen.
  iPersist "n order".

  iAssert (∃ (i: w64),
              "Hs" ∷ s ↦* ((W64 <$> seqZ 0 (sint.Z i)) ++ replicate (sint.nat n - sint.nat i) (W64 0)) ∗
              "i" ∷ i_ptr ↦ i ∗
              "%Hi" ∷ ⌜0 ≤ sint.Z i ≤ sint.Z n⌝)%I
    with "[$i Hs]" as "IH".
  { iFrame.
    iSplit; [ | word ].
    iExactEq "Hs".
    rewrite /named.
    repeat f_equal.
    rewrite seqZ_nil /=; [ | word ].
    f_equal. word.
  }
  wp_for "IH".
  destruct (bool_decide_reflect (uint.Z i < uint.Z n)); wp_auto.
  - rewrite -> decide_True; last word. wp_auto.
    wp_apply (wp_store_slice_index with "[$Hs]").
    { len. }
    iIntros "Hs".
    wp_auto. wp_for_post.
    iFrame.
    iSplit; [ | word ].
    rewrite /named.
    iExactEq "Hs".
    f_equal.
    replace (sint.nat (word.add i (W64 1))) with (S (sint.nat i)) by word.
    replace (sint.Z (word.add i (W64 1))) with (sint.Z i + 1) by word.
    rewrite insert_app_r_alt; [ | len ].
    autorewrite with len.
    replace (sint.nat i - sint.nat i)%nat with 0%nat by word.
    replace (sint.nat n - sint.nat i)%nat with
      (S (sint.nat n - sint.nat i - 1)%nat) by word.
    rewrite replicate_S /=.
    rewrite cons_middle.
    rewrite app_assoc.
    f_equal.
    + rewrite seqZ_plus_1; [ | word ].
      rewrite Z.add_0_l.
      rewrite fmap_app /=.
      repeat f_equal.
      word.
    + f_equal; word.
  - wp_apply (wp_Shuffle with "[$Hs]").
    iIntros (xs') "[%Hperm Hs]".
    wp_auto.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    rewrite -Hperm.
    assert (i = n) by word; subst.
    replace (sint.nat n - sint.nat n)%nat with 0%nat by word.
    rewrite replicate_0 app_nil_r.
    auto.
Qed.

End wps.
