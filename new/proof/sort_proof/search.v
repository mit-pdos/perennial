From stdpp Require Import sorting.
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
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : sort.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) sort := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) sort := build_get_is_pkg_init_wf.
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
      ⌜0 ≤ sint.Z i⌝ ∗
      ⌜(sint.Z i < sint.Z n)%Z → f (sint.Z i) = true⌝ ∗
      ⌜(∀ i, 0 ≤ i < sint.Z n → f i = false) → sint.Z i = sint.Z n⌝ ∗
      ⌜∀ k, 0 ≤ k < sint.Z i → f k = false⌝
  }}}.
Proof using W.
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
    * word.
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

(** TODO: should be equivalent to StronglySorted, but couldn't find a std++
lemma relating that to list lookup. *)
Definition list_sorted {A} (R: A → A → Prop) (l: list A) :=
  ∀ (i j: nat), (i < j)%nat →
                ∀ (xi xj: A),
                  l !! i = Some xi → l !! j = Some xj →
                R xi xj.

Definition search_f (x: w64) (xs: list w64) : Z → bool :=
  λ i, match xs !! (Z.to_nat i) with
       | Some x0 => bool_decide (sint.Z x ≤ sint.Z x0)
       | None => true (* arbitrary, unreachable *)
       end.

Lemma search_f_true x xs i x_i :
  xs !! (Z.to_nat i) = Some x_i →
  search_f x xs i = true ↔
  sint.Z x ≤ sint.Z x_i.
Proof.
  rewrite /search_f.
  intros ->.
  rewrite bool_decide_eq_true //.
Qed.

Lemma search_f_false x xs i x_i :
  xs !! (Z.to_nat i) = Some x_i →
  search_f x xs i = false ↔
  sint.Z x_i < sint.Z x.
Proof.
  rewrite /search_f.
  intros ->.
  rewrite bool_decide_eq_false //.
  word.
Qed.

Lemma wp_SearchInts (a: slice.t) (x: w64) q (xs: list w64) :
  {{{ is_pkg_init sort ∗ a ↦*{q} xs ∗ ⌜ list_sorted (λ (i j: w64), sint.Z i ≤ sint.Z j) xs ⌝ }}}
    @! sort.SearchInts #a #x
  {{{ (i: w64), RET #i; a ↦*{q} xs ∗
      ⌜(∀ (j: nat) x0, Z.of_nat j < sint.Z i → xs !! j = Some x0 → sint.Z x0 < sint.Z x) ∧
       (∀ (j: nat) x0, sint.Z i ≤ Z.of_nat j → xs !! j = Some x0 → sint.Z x ≤ sint.Z x0)
      ⌝ }}}.
Proof using W.
  wp_start as "[Ha %Hsort]".
  wp_auto.
  iDestruct (own_slice_len with "Ha") as %Hlen.
  iPersist "x a".
  wp_apply (wp_Search _ _ (search_f x xs) (a ↦*{q} xs) with "[$Ha]").
  {
    iSplit; first word.
    iSplit.
    - iIntros (i). wp_start as "[Ha %Hbound]".
      wp_auto.
      list_elem xs (sint.Z i) as x_i.
      rewrite -> decide_True; last word.
      wp_apply (wp_load_slice_index with "[$Ha]") as "Ha"; [ word | eauto | ].
      iApply "HΦ". iFrame.
      iPureIntro.
      rewrite /search_f.
      rewrite Hx_i_lookup.
      apply bool_decide_ext.
      word.
    - iPureIntro.
      rewrite /is_mono_pred; intros **.
      list_elem xs (Z.to_nat i) as x_i.
      list_elem xs (Z.to_nat j) as x_j.
      rewrite search_f_true in H0; [ | eauto ].
      rewrite search_f_true; [ | eauto ].
      etrans; eauto.
      eapply Hsort; [ | eauto | eauto ]; word.
  }

  iIntros (i) "[Ha %Hsearch]".
  wp_auto.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  destruct Hsearch as (Hi_nn & Hfound & Hoob & Hgt).
  destruct (decide (sint.Z i < sint.Z a.(slice.len))).
  {
    (* returned index is in-bounds *)
    specialize (Hfound ltac:(word)).
    list_elem xs (sint.nat i) as xi.
    rewrite search_f_true in Hfound; [ | eauto ].
    split.
    - intros j xj Hj_bound Hget_j.
      pose proof (Hgt (Z.of_nat j) ltac:(word)) as Hget_j'.
      rewrite search_f_false in Hget_j'; [ | rewrite Nat2Z.id; eauto ].
      word.
    - intros j xj Hj_bound Hget_j.
      destruct (decide (sint.nat i = j)).
      {
        subst.
        rewrite Hxi_lookup in Hget_j.
        assert (xi = xj) by congruence; subst.
        word.
      }
      pose proof (Hsort (sint.nat i) j ltac:(word) _ _ ltac:(eauto) ltac:(eauto)).
      simpl in *.
      word.
  }
  (* i is out-of-bounds (larger than list length) *)
  split.
  - intros.
    (* every element is less than i *)
    pose proof (Hgt j ltac:(word)) as Hsearchj.
    rewrite search_f_false in Hsearchj; [ | rewrite Nat2Z.id; eauto ].
    word.
  - (* vacuous, no elements after index i *)
    intros j xj Hj_bound Hget_j.
    apply lookup_lt_Some in Hget_j. word.
Qed.

End proof.
