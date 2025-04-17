From New.proof Require Import proof_prelude.
From New.code.github_com.goose_lang Require Import std.
Require Export New.generatedproof.github_com.goose_lang.std.
From New.proof Require Import primitive sync.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!std.GlobalAddrs}.

#[global]
Program Instance : IsPkgInit std :=
  ltac2:(build_pkg_init ()).

Lemma wp_Assert (cond : bool) :
  {{{ is_pkg_init std ∗ ⌜cond = true⌝ }}}
    std @ "Assert" #cond
  {{{ RET #(); True }}}.
Proof.
  wp_start as "%". subst.
  wp_auto.
  by iApply "HΦ".
Qed.

Lemma wp_SumNoOverflow (x y : u64) :
  {{{ is_pkg_init std }}}
    std @ "SumNoOverflow" #x #y
  {{{ RET #(bool_decide (uint.Z (word.add x y) = (uint.Z x + uint.Z y)%Z)); True }}}.
Proof.
  wp_start as "_".
  wp_auto.
  iSpecialize ("HΦ" with "[$]").
  iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  pose proof (sum_overflow_check x y).
  word.
Qed.

Lemma wp_SumAssumeNoOverflow (x y : u64) :
  {{{ is_pkg_init std }}}
    std @ "SumAssumeNoOverflow" #x #y
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
  {{{ is_pkg_init std }}}
    std @ "MulNoOverflow" #x #y
  {{{ RET #(bool_decide (uint.Z (word.mul x y) = (uint.Z x * uint.Z y)%Z)); True }}}.
Proof.
  wp_start as "_".
  wp_auto.
  destruct (bool_decide_reflect (x = W64 0)); wp_auto.
  { subst. rewrite -> bool_decide_eq_true_2 by word.
    iApply "HΦ"; auto. }
  destruct (bool_decide_reflect (y = W64 0)); wp_auto.
  { subst. rewrite -> bool_decide_eq_true_2 by word.
    iApply "HΦ"; auto. }
  iSpecialize ("HΦ" with "[$]").
  iExactEq "HΦ".
  repeat f_equal.
  apply bool_decide_ext.
  pose proof (mul_overflow_check_correct x y ltac:(word) ltac:(word)).
  word.
Qed.

Lemma wp_MulAssumeNoOverflow (x y : u64) :
  {{{ is_pkg_init std }}}
    std @ "MulAssumeNoOverflow" #x #y
  {{{ RET #(word.mul x y); ⌜uint.Z (word.mul x y) = (uint.Z x * uint.Z y)%Z⌝ }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply wp_MulNoOverflow.
  wp_apply wp_Assume as "%Hassume".
  rewrite bool_decide_eq_true in Hassume.
  iApply "HΦ". iPureIntro. done.
Qed.

Definition is_JoinHandle (l: loc) (P: iProp Σ): iProp _ :=
  ∃ (mu_l cond_l: loc),
  "#mu" ∷ l ↦s[std.JoinHandle :: "mu"]□ mu_l ∗
  "#cond" ∷ l ↦s[std.JoinHandle :: "cond"]□ cond_l ∗
  "#Hcond" ∷ is_Cond cond_l (interface.mk sync "Mutex'ptr"%go #mu_l) ∗
  "#Hlock" ∷ is_Mutex mu_l
     (∃ (done_b: bool),
         "done_b" ∷ l ↦s[std.JoinHandle :: "done"] done_b ∗
         "HP" ∷ if done_b then P else True)
.

Lemma wp_newJoinHandle (P: iProp Σ) :
  {{{ is_pkg_init std }}}
    std @ "newJoinHandle" #()
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_alloc mu as "?".
  wp_auto.
  wp_apply (wp_NewCond with "[#]") as "%cond #His_cond".
  wp_alloc jh_l as "jh".
  iApply struct_fields_split in "jh". simpl. iNamed "jh".
  iPersist "Hmu Hcond".
  iMod (init_Mutex (∃ (done_b: bool),
         "done_b" ∷ jh_l ↦s[std.JoinHandle :: "done"] done_b ∗
         "HP" ∷ if done_b then P else True)
         with "[$] [$]") as "Hlock".
  wp_auto.
  iApply "HΦ".
  rewrite /is_JoinHandle.
  iFrame "His_cond #". iFrame.
Qed.

Lemma wp_JoinHandle__finish l (P: iProp Σ) :
  {{{ is_pkg_init std ∗ is_JoinHandle l P ∗ P }}}
    l @ std @ "JoinHandle'ptr" @ "finish" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "[Hhandle P]".
  iNamed "Hhandle".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[locked Hinv]".
  iNamed "Hinv".
  wp_auto.
  wp_apply (wp_Cond__Signal with "[$Hcond]").
  wp_apply (wp_Mutex__Unlock with "[$Hlock $locked done_b P]").
  { iFrame "done_b P". }
  iApply "HΦ".
  done.
Qed.

Lemma wp_Spawn (P: iProp Σ) (f : func.t) :
  {{{ is_pkg_init std ∗
        (∀ Φ, ▷(P -∗ Φ #()) -∗ WP #f #() {{ Φ }}) }}}
  std @ "Spawn" #f
  {{{ (l: loc), RET #l; is_JoinHandle l P }}}.
Proof.
  wp_start as "Hwp".
  wp_auto.
  wp_apply (wp_newJoinHandle P) as "%l #Hhandle".
  iPersist "f h".
  wp_apply (wp_fork with "[Hwp]").
  - (* NOTE: it's important not to do a pure reduction here since it would
    produce a substitution into the lambda *)
    wp_apply "Hwp".
    iIntros "HP".
    wp_auto.
    wp_apply (wp_JoinHandle__finish with "[$Hhandle $HP]").
    done.
  - iApply "HΦ".
    iFrame "#".
Qed.

Lemma wp_JoinHandle__Join l P :
  {{{ is_pkg_init std ∗ is_JoinHandle l P }}}
    l @ std @ "JoinHandle'ptr" @ "Join" #()
  {{{ RET #(); P }}}.
Proof.
  wp_start as "Hjh". iNamed "Hjh".
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked Hlinv]". iNamed "Hlinv".
  wp_auto.

  iAssert (∃ (done_b: bool),
           "locked" ∷ own_Mutex mu_l ∗
           "done" ∷ l ↦s[std.JoinHandle::"done"] done_b ∗
           "HP" ∷ (if done_b then P else True))%I
          with "[$Hlocked $done_b $HP]" as "HI".
  wp_for "HI".
  destruct done_b0; wp_auto.
  - wp_for_post.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $locked $done]").
    iApply "HΦ". done.
  - wp_apply (wp_Cond__Wait with "[$Hcond locked done HP]") as "H".
    { iSplit.
      - iApply (Mutex_is_Locker with "[] Hlock"). iPkgInit.
      - iFrame. }
    iDestruct "H" as "[Hlocked Hlinv]". iNamed "Hlinv".
    wp_for_post.
    iFrame.
Qed.

#[local] Unset Printing Projections.

Lemma wp_Shuffle s (xs: list w64) :
  {{{ is_pkg_init std ∗ s ↦* xs }}}
    std @ "Shuffle" #s
  {{{ xs', RET #(); ⌜Permutation xs xs'⌝ ∗
                      s ↦* xs' }}}.
Proof.
  wp_start as "Hs".
  wp_auto.
  iPersist "xs".
  iDestruct (own_slice_len with "Hs") as %Hlen.
  destruct (bool_decide_reflect (slice.len_f s = W64 0)); wp_auto.
  {
    assert (xs = []); subst .
    { destruct xs; auto; simpl in *; word.  }
    iApply "HΦ".
    iFrame. auto.
  }
  iAssert (∃ (i: w64) (xs': list w64),
              "i" ∷ i_ptr ↦ i ∗
              "%HI" ∷ ⌜0 ≤ uint.Z i < uint.Z (slice.len_f s)⌝ ∗
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
    wp_pure; first word.

    list_elem xs' i as x_i.
    wp_apply (wp_load_slice_elem with "[$Hs]").
    { eauto. }
    iIntros "Hs".
    wp_auto.

    list_elem xs' (uint.nat (word.modu x (word.add i (W64 1)))) as x_i'.
    wp_pure; first word.
    wp_apply (wp_load_slice_elem with "[$Hs]").
    { eauto. }
    iIntros "Hs".

    wp_auto.
    wp_pure; first word.
    wp_apply (wp_store_slice_elem with "[$Hs]").
    { word. }
    iIntros "Hs".
    wp_auto.
    wp_pure; first word.
    wp_apply (wp_store_slice_elem with "[$Hs]").
    { len. }
    iIntros "Hs".
    wp_auto. wp_for_post.
    iFrame.
    iPureIntro.
    split; [ word | ].
    trans xs'; auto.
    admit. (* swap on list is a permutation *)
  - wp_auto.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    auto.
Admitted.

Lemma seqZ_plus_1 n m :
  0 ≤ m →
  seqZ n (m + 1) = seqZ n m ++ [n + m].
Proof.
  intros.
  rewrite seqZ_app; try lia.
  reflexivity.
Qed.

Lemma wp_Permutation (n: w64) :
  {{{ is_pkg_init std }}}
    std@ "Permutation" #n
  {{{ xs s, RET #s;
      ⌜xs ≡ₚ (W64 <$> seqZ 0 (uint.Z n))⌝ ∗
      s ↦* xs
  }}}.
Proof.
  wp_start as "_".
  wp_auto.
  wp_apply (wp_slice_make2 (V:=w64)). iIntros (s) "[Hs _]".
  wp_auto.
  iDestruct (own_slice_len with "Hs") as "%Hlen".
  autorewrite with len in Hlen.
  iPersist "n order".

  iAssert (∃ (i: w64),
              "Hs" ∷ s ↦* ((W64 <$> seqZ 0 (uint.Z i)) ++ replicate (uint.nat n - uint.nat i) (W64 0)) ∗
              "i" ∷ i_ptr ↦ i ∗
              "%Hi" ∷ ⌜uint.Z i ≤ uint.Z n⌝)%I
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
  - wp_pure; first word.
    wp_apply (wp_store_slice_elem with "[$Hs]").
    { len. }
    iIntros "Hs".
    wp_auto. wp_for_post.
    iFrame.
    iSplit; [ | word ].
    rewrite /named.
    iExactEq "Hs".
    f_equal.
    replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
    replace (uint.Z (word.add i (W64 1))) with (uint.Z i + 1) by word.
    rewrite insert_app_r_alt; [ | len ].
    autorewrite with len.
    replace (uint.nat i - uint.nat i)%nat with 0%nat by word.
    replace (uint.nat n - uint.nat i)%nat with
      (S (uint.nat n - uint.nat i - 1)%nat) by word.
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
    replace (uint.nat n - uint.nat n)%nat with 0%nat by word.
    rewrite replicate_0 app_nil_r.
    auto.
Qed.

End wps.
