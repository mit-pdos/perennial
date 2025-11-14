From New.generatedproof Require Import sort.
From New.proof Require Import proof_prelude.
From New.proof.sort_proof Require Import sort_init.

(** Proof of sort.Search.

The specification for sort.Search is simpler than sort.Find: it takes a
predicate function (f: Z → bool) and a number n, and it searches for the first
i ∈ [0, n) such that [f i = true], assuming [f] goes from false to true.

The intuition behind f is that if you're searching for x in a sorted list xs,
then f(i) = (xs[i] >= x), but in principle Search is much more general.

There are several key ideas in adapting the informal specification and the proof
sketch in the Go source code:
- The natural specification does not extend nicely to _negative_ n - this edge
  case was likely overlooked. So we make it a precondition that 0 ≤ n.
- The predicate function is assumed to transition from false to true at most
  once. It only matters whether the function returns true or false at each index.
- The predicate function is only ever called on [0, n), so we promise this in
  the Hoare triple assumed for f_code (the implementation of f, a pure function).
- The proof sketch "defines" f(-1) = false and f(n) = true, which makes the
  invariants much easier to state. We do not want to impose this on the caller,
  so we "adapt" the user-provided f function to have this property. There is
  no loss because the provided function is anyway not called on these
  out-of-bounds values.
*)

(* This proof was greatly assisted by Claude Code (with Sonnet 4.5), adapting
the sort.Find proof and spec based on the Go code. It didn't get all the proofs
right but fixing it was mostly fixing tactic invocations and driving lia a bit
better. And its comments in the proof were actually helpful. *)

Unset Printing Projections.

Section proof.
Context  `{hG: heapGS Σ, !ffi_semantics _ _} `{!globalsGS Σ} {go_ctx : GoContext}.

(* The predicate function must implement a pure boolean function over in-bounds
   indices, with an arbitrary invariant I that it requires and preserves *)
Definition pred_implements (f_code: func.t) (f: Z → bool) (n: Z) (I: iProp Σ) : iProp Σ :=
  ∀ (i: w64),
    {{{ I ∗ ⌜0 ≤ sint.Z i < n⌝ }}}
      #f_code #i
    {{{ (r: bool), RET #r; I ∗ ⌜r = f (sint.Z i)⌝ }}}.

#[export] Instance pred_implements_persistent f_code f n I `{!Persistent I} :
  Persistent (pred_implements f_code f n I).
Proof. apply _. Qed.

(* "proper" monotonicity on only [0, n) - a sensible precondition for Search *)
Definition is_mono_pred (f: Z → bool) (n: Z) : Prop :=
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < n → f i = true → f j = true).

Definition adapt_pred (f: Z → bool) (n: Z) : Z → bool :=
  λ i, if decide (i < 0) then false else
         if decide (n ≤ i) then true
         else f i.

Lemma adapt_pred_bounded f n :
  ∀ i, 0 ≤ i < n →
       adapt_pred f n i = f i.
Proof.
  intros i H.
  rewrite /adapt_pred.
  repeat destruct (decide _); try lia; auto.
Qed.

(* "internal" monotonicity on [-1, n] by extending (adapting) f *)
Definition is_valid_pred (f: Z → bool) (n: Z) : Prop :=
  (∀ i j, -1 ≤ i ∧ i < j ∧ j ≤ n → f i = true → f j = true) ∧
  f (-1) = false ∧
  f n = true.

Lemma is_valid_pred_adapted f n :
  0 ≤ n →
  is_mono_pred f n →
  is_valid_pred (adapt_pred f n) n.
Proof.
  rewrite /is_mono_pred /is_valid_pred.
  intros Hnn Hmono.
  split_and!.
  - intros i j Hij Hfi.
    assert (i < j) as Hlt by lia.
    destruct (decide (0 ≤ i ∧ j < n)).
    { repeat rewrite -> adapt_pred_bounded by lia.
      apply (Hmono i j); [ lia | ].
      move: Hfi. rewrite /adapt_pred.
      repeat destruct decide; try lia; auto. }
    rewrite /adapt_pred in Hfi |- *.
    repeat destruct decide; try lia; auto.
  - rewrite /adapt_pred.
    repeat destruct decide; lia.
  - rewrite /adapt_pred.
    repeat destruct decide; try lia; auto.
Qed.

Lemma pred_implements_adapt f_code f n I :
  pred_implements f_code f n I -∗
  pred_implements f_code (adapt_pred f n) n I.
Proof.
  rewrite /pred_implements.
  iIntros "#H %i".
  wp_start as "[HI %Hbound]".
  iApply ("H" with "[$HI //]").
  rewrite adapt_pred_bounded; [ | lia ].
  done.
Qed.

Lemma wp_Search (n: w64) (f_code: func.t) (f: Z → bool) (I: iProp Σ) :
  {{{ is_pkg_init sort ∗
      ⌜0 ≤ sint.Z n⌝ ∗
      pred_implements f_code f (sint.Z n) I ∗
      I ∗
      ⌜is_mono_pred f (sint.Z n)⌝ }}}
    @! sort.Search #n #f_code
  {{{ (i: w64), RET #i;
      I ∗
      ⌜(sint.Z i < sint.Z n)%Z → f (sint.Z i) = true⌝ ∗
      ⌜(∀ i, 0 ≤ i < sint.Z n → f i = false) → sint.Z i = sint.Z n⌝ ∗
      ⌜∀ k, 0 ≤ k < sint.Z i → f k = false⌝
  }}}.
Proof.
  wp_start as "(%Hpos & #Hf0 & I & %Hvalid)".
  wp_auto.

  iDestruct (pred_implements_adapt with "Hf0") as "Hf".
  iClear "Hf0".
  apply is_valid_pred_adapted in Hvalid; [ | lia ].

  (* Initialize loop invariant: i = 0, j = n *)
  iAssert (
    ∃ (i j: w64),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "I" ∷ I ∗
      "%Hbounds" ∷ ⌜0 ≤ sint.Z i ≤ sint.Z j ≤ sint.Z n⌝ ∗
      "%Hi_prop" ∷ ⌜adapt_pred f (sint.Z n) (sint.Z i - 1) = false⌝ ∗
      "%Hj_prop" ∷ ⌜adapt_pred f (sint.Z n) (sint.Z j) = true⌝
  )%I with "[$I $i $j]" as "HI".
  { iPureIntro. split; [ word | ].
    destruct Hvalid as (Hmono & Hneg & Hn).
    change (sint.Z (W64 0)-1) with (-1).
    split; auto.
  }

  wp_for "HI".
  wp_if_destruct.
  - (* Loop body: i < j *)
    (* Call f(h) *)
    wp_apply ("Hf" with "[$I]").
    { iPureIntro. word. }
    iIntros (r) "[HI %Hf_result]".
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
    + (* !f(h), so f(h) = false, so i = h + 1 *)
      wp_for_post.
      iFrame.
      iPureIntro.
      split; [word|].
      destruct Hvalid as (Hmono & Hneg & Hn).
      replace (sint.Z (word.add h (W64 1)) - 1) with (sint.Z h) by word.
      destruct (adapt_pred f (sint.Z n) (sint.Z h)); auto.
    + (* f(h) = true, so j = h *)
      wp_for_post.
      iFrame.
      iPureIntro.
      split; [word|].
      replace (sint.Z (word.add h (W64 1)) - 1) with (sint.Z h) by word.
      auto.
  - (* Loop exit: i = j *)
    assert (sint.Z i = sint.Z j) by word.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split_and!.
    * intros Hilt.
      destruct (decide (sint.Z i < sint.Z n)); [ | word ].
      rewrite -> !adapt_pred_bounded in * by lia.
      destruct Hvalid as (Hmono & Hneg & Hn).
      destruct (f (sint.Z i)) eqn:Hfi; auto.
      (* contradiction: f(i-1) = false but f(i) = false, yet f(j) = f(i) must be true *)
      assert (sint.Z i - 1 < sint.Z i) by lia.
      destruct (decide (sint.Z i = 0)).
      { (* i = 0, so j = 0, but we know f(j) = true *)
        subst.
        change (sint.Z (W64 0)) with 0 in *.
        congruence.
      }
      (* i > 0, so i-1 is in bounds *)
      rewrite -> adapt_pred_bounded in Hi_prop by lia.
      (* We have f(i-1) = false and f(i) = false, but f(j) = true and i = j *)
      subst. congruence.
    * intros Hno_true.
      destruct (decide (sint.Z i < sint.Z n)); [ | word ].
      (* contradiction: if i < n, then f(i) = true by the invariant *)
      exfalso.
      rewrite -> adapt_pred_bounded in Hj_prop by lia.
      pose proof (Hno_true (sint.Z i) ltac:(lia)). congruence.
    * intros k Hk.
      destruct Hvalid as (Hmono & Hneg & Hn).
      rewrite -> !adapt_pred_bounded in * by lia.
      destruct (decide (k = sint.Z i - 1)).
      { subst. auto. }
      destruct (decide (k < sint.Z i - 1)).
      { (* use monotonicity: if f(k) = true, then f(i-1) = true, contradiction *)
        destruct (f k) eqn:Hfk; auto.
        assert (adapt_pred f (sint.Z n) (sint.Z i - 1) = true).
        { apply (Hmono k (sint.Z i - 1)); try lia.
          rewrite -> adapt_pred_bounded by lia. auto. }
        rewrite -> adapt_pred_bounded in * by lia.
        congruence.
      }
      lia.
Qed.

End proof.
