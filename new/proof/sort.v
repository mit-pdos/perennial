From New.generatedproof Require Import sort.
From New.proof Require Import proof_prelude.

Unset Printing Projections.

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

Definition signum (cmp_r: Z) : Z :=
  if decide (cmp_r < 0) then -1
  else if decide (cmp_r = 0) then 0
       else 1.

(* precondition for Find *)
Definition is_valid_cmp (cmp: Z → Z) (n: Z) : Prop :=
  (∀ i j, -1 ≤ i ∧ i < j ≤ n → signum (cmp j) ≤ signum (cmp i)) ∧
  (* NOTE: this is just a useful definition to make the invariant simpler, the
  actual comparison function is never passed there parameters *)
  (cmp (-1) = 1) ∧
  (cmp n ≤ 0).

Lemma wp_Find (n: w64) (cmp_code: func.t) (cmp: Z → Z) (I: iProp Σ) :
  {{{ is_pkg_init sort ∗
      ⌜0 ≤ sint.Z n⌝ ∗
      cmp_implements cmp_code cmp (sint.Z n) I ∗
      I ∗
      ⌜is_valid_cmp cmp (sint.Z n)⌝ }}}
    @! sort.Find #n #cmp_code
  {{{ (i: w64) (found: bool), RET (#i, #found);
      I ∗
      ⌜found = true ↔
        sint.Z i < sint.Z n ∧
        cmp (sint.Z i) = 0⌝ ∗
      ⌜(∀ i, 0 ≤ i < sint.Z n → cmp i > 0) → sint.Z i = sint.Z n⌝ ∗
      ⌜∀ k, 0 ≤ k < sint.Z i → cmp k > 0⌝
  }}}.
Proof.
  wp_start as "(%Hpos & #Hcmp & I & %Hvalid)".
  wp_auto.

  (* Initialize loop invariant: i = 0, j = n *)
  iAssert (
    ∃ (i j: w64),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "I" ∷ I ∗
      "%Hbounds" ∷ ⌜0 ≤ sint.Z i ≤ sint.Z j ≤ sint.Z n⌝ ∗
      "%Hi_prop" ∷ ⌜cmp (sint.Z i - 1) > 0⌝ ∗
      "%Hj_prop" ∷ ⌜cmp (sint.Z j) ≤ 0⌝
  )%I with "[$I $i $j]" as "HI".
  { iPureIntro. split; [ word | ].
    destruct Hvalid as (Hmono & Hneg & Hn).
    change (sint.Z (W64 0)-1) with (-1).
    split; word.
  }

  wp_for "HI".
  wp_if_destruct.
  - (* Loop body: i < j *)
    (* Call cmp(h) *)
    wp_apply ("Hcmp" with "[$I]").
    { iPureIntro. word. }
    iIntros (r) "[HI %Hcmp_result]".
    (* note that making this a definition hides it from word (a subst is
    needed) *)
    set (h:=word.sru (word.add i j) (W64 1)) in *.
    (* we can use h using only this abstract property *)
    assert (sint.Z i ≤ sint.Z h < sint.Z j) as Hj.
    {
      subst h.
      word.
    }

    wp_auto.
    wp_if_destruct.
    + (* cmp(h) > 0, so i = h + 1 *)
      wp_for_post.
      iFrame.
      iPureIntro.
      split; [word|].
      split; [ | word ].
      destruct Hvalid as (Hmono & Hneg & Hn).
      pose proof (Hmono (sint.Z i - 1) (sint.Z h) ltac:(word)).
      replace (sint.Z (word.add h (W64 1)) - 1) with (sint.Z h) by word.
      word.
    + (* cmp(h) ≤ 0, so j = h *)
      wp_for_post.
      iFrame.
      iPureIntro.
      split; [word|].
      split; [word|].
      destruct Hvalid as (Hmono & Hneg & Hn).
      pose proof (Hmono (sint.Z h) (sint.Z j) ltac:(word)).
      word.
  - (* Loop exit: i = j *)
    assert (sint.Z i = sint.Z j) by word.
    wp_if_destruct.
    + (* i < n, check if cmp(i) = 0 *)
      wp_apply ("Hcmp" with "[$I]").
      { word. }
      iIntros (r) "[I %Hcmp_result]".
      wp_auto.

      iApply "HΦ".
      iFrame.
      iPureIntro.
      rewrite bool_decide_eq_true.
      split_and!.
      * word.
      * intros Hno_index.
        (* contradiction in the i < n case *)
        pose proof (Hno_index (sint.Z j) ltac:(word)).
        word.
      * intros k Hk.
        destruct Hvalid as (Hmono & Hneg & Hn).
        destruct (decide (k = sint.Z i - 1)).
        { subst; word. }
        pose proof (Hmono k (sint.Z i-1) ltac:(word)) as Hmono'.
        move: Hmono'. rewrite /signum.
        repeat destruct decide; try lia.
    + (* i = n *)
      iApply "HΦ".
      iFrame.
      iPureIntro.
      split_and!.
      * word.
      * intros Hno_index.
        word.
      * intros k Hk.
        destruct Hvalid as (Hmono & Hneg & Hn).
        destruct (decide (k = sint.Z i - 1)).
        { subst; word. }
        pose proof (Hmono k (sint.Z i-1) ltac:(word)) as Hmono'.
        move: Hmono'. rewrite /signum.
        repeat destruct decide; try lia.
Qed.

Definition adapt_cmp (cmp: Z → Z) (n: Z) : Z → Z :=
  λ i, if decide (i < 0) then (1) else
         if decide (n ≤ i) then
           if decide (n = 0) then 0 else signum (cmp (n-1))
         else signum (cmp i).

Definition real_valid_cmp (cmp: Z → Z) (n: Z) :=
  ∃ start end_,
    (0 ≤ start ≤ end_ ∧ end_ < n) ∧
    (∀ i, 0 ≤ i < start     → cmp i > 0) ∧
    (∀ i, start ≤ i < end_  → cmp i = 0) ∧
    (∀ i, end_ ≤ i < n      → cmp i < 0).

Ltac saturate cmp :=
  repeat
    match goal with
    | _ => lia
    | H: context[cmp ?i], Hall: ∀ (_: Z), _ |- _ =>
      learn_hyp (Hall i)
    end.

Lemma real_to_internal_cmp cmp n :
  0 ≤ n →
  real_valid_cmp cmp n →
  is_valid_cmp (adapt_cmp cmp n) n.
Proof.
  intros Hnn H.
  destruct H as (start & end_ & Hord & Hstart & Hmiddle & Hend).
  split_and!.
  - intros i j H.
    rewrite /adapt_cmp /signum.
    repeat destruct (decide _); saturate cmp.
  - rewrite /adapt_cmp /signum.
    repeat destruct (decide _); lia.
  - rewrite /adapt_cmp /signum.
    repeat destruct (decide _); saturate cmp.
Qed.

Lemma adapt_cmp_bounded cmp n :
  ∀ i, 0 ≤ i < n →
       signum (cmp i) = adapt_cmp cmp n i.
Proof.
  intros i H.
  rewrite /adapt_cmp.
  repeat destruct (decide _); try lia.
Qed.

(* TODO: cmp_implements does not carry over to adapt_cmp cmp *)

End proof.
