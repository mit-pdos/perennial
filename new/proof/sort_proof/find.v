From New.generatedproof Require Import sort.
From New.proof Require Import proof_prelude.
From New.proof.sort_proof Require Import sort_init.

(** Proof of sort.Find.

The specification for sort.Find is fairly complicated: it takes a comparison
function (cmp: Z → Z) and a number n, and it searches for an i ∈ [0, n) such
that [cmp i = 0] and [cmp (i-1) > 0], assuming [cmp] goes from positive to zero
to negative.

The intuition behind cmp is that if you're searching for x in a sorted list xs,
then cmp(i) = xs[i] - x, but in principle Find is much more general.

There are several key ideas in adapting the informal specification and the proof
sketch in the Go source code:
- The natural specification does not extend nicely to _negative_ n - this edge
  case was likely overlooked (the specification implies n would be returned but
  0 is instead). So we make it a precondition that 0 ≤ n.
- The comparison function is assumed to have a monotonic _sign_. It only ever
  matters what the sign (-1, 0, or 1) of a comparison is in any case.
- The comparison function is only ever called on [0, n), so we promise this in
  the Hoare triple assumed for cmp_code (the implementation of cmp, a pure
  function).
- The proof sketch "defines" cmp (-1) = 1 and cmp n ≤ 0, which makes the
  invariants much easier to state. We do not want to impose this on the caller,
  so we "adapt" the user-provided cmp function to have this property. There is
  no loss because the provided function is anyway not called on these
  out-of-bounds values.
*)

Unset Printing Projections.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : sort.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) sort := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) sort := build_get_is_pkg_init_wf.
(* The comparison function must implement a pure function over in-bounds indices,
   with an arbitrary invariant I that it requires and preserves *)
Definition cmp_implements (cmp_code: func.t) (cmp: Z → Z) (n: Z) (I: iProp Σ) : iProp Σ :=
  ∀ (i: w64),
    {{{ I ∗ ⌜0 ≤ sint.Z i < n⌝ }}}
      #cmp_code #i
    {{{ (r: w64), RET #r; I ∗ ⌜sint.Z r = cmp (sint.Z i)⌝ }}}.

#[export] Instance cmp_implements_persistent cmp_code cmp n I `{!Persistent I} :
  Persistent (cmp_implements cmp_code cmp n I).
Proof. apply _. Qed.

Definition signum (cmp_r: Z) : Z :=
  if decide (cmp_r < 0) then -1
  else if decide (cmp_r = 0) then 0
       else 1.

Lemma signum_n1 : signum (-1) = (-1).
Proof. reflexivity. Qed.
Lemma signum_0 : signum 0 = 0.
Proof. reflexivity. Qed.
Lemma signum_1 : signum 1 = 1.
Proof. reflexivity. Qed.
Lemma signum_idemp cmp_r :
  signum (signum cmp_r) = signum cmp_r.
Proof.
  rewrite /signum.
  repeat destruct decide; lia.
Qed.
Lemma signum_bound cmp_r :
  -1 ≤ signum cmp_r ≤ 1.
Proof.
  rewrite /signum.
  repeat destruct decide; lia.
Qed.

(* "proper" monotonicity on only [0, n) - a sensible precondition for Find *)
Definition is_mono_cmp (cmp: Z → Z) (n: Z) : Prop :=
  (∀ i j, 0 ≤ i ∧ i < j < n → signum (cmp j) ≤ signum (cmp i)).

Hint Rewrite signum_n1 signum_0 signum_1 signum_idemp : sign.
Hint Resolve signum_bound : sign.

Definition adapt_cmp (cmp: Z → Z) (n: Z) : Z → Z :=
  λ i, if decide (i < 0) then (1) else
         if decide (n ≤ i) then
           if decide (n = 0) then 0 else (-1)
         else cmp i.

Lemma adapt_cmp_bounded cmp n :
  ∀ i, 0 ≤ i < n →
       adapt_cmp cmp n i = cmp i.
Proof.
  intros i H.
  rewrite /adapt_cmp.
  repeat destruct (decide _); try lia.
Qed.

(* "internal" monotonicity on [-1, n] by extending (adapting) cmp *)
Definition is_valid_cmp (cmp: Z → Z) (n: Z) : Prop :=
  (∀ i j, -1 ≤ i ∧ i < j ≤ n → signum (cmp j) ≤ signum (cmp i)) ∧
  cmp (-1) = 1 ∧
  cmp n ≤ 0.

Lemma is_valid_cmp_adapted cmp n :
  0 ≤ n →
  is_mono_cmp cmp n →
  is_valid_cmp (adapt_cmp cmp n) n.
Proof.
  rewrite /is_mono_cmp /is_valid_cmp.
  intros Hnn Hmono.
  split_and!.
  - intros **. pose proof (Hmono i j) as Hij.
    assert (i < j) by lia.
    destruct (decide (0 ≤ i ∧ j < n)).
    { repeat rewrite -> adapt_cmp_bounded by lia.
      lia. }
    rewrite /adapt_cmp.
    repeat destruct decide; autorewrite with sign; try lia.
    + pose proof (signum_bound (cmp i)); lia.
    + pose proof (signum_bound (cmp j)); lia.
  - rewrite /adapt_cmp.
    repeat destruct decide; lia.
  - rewrite /adapt_cmp.
    repeat destruct decide; lia.
Qed.

Lemma cmp_implements_adapt cmp_code cmp n I :
  cmp_implements cmp_code cmp n I -∗
  cmp_implements cmp_code (adapt_cmp cmp n) n I.
Proof.
  rewrite /cmp_implements.
  iIntros "#H %i".
  wp_start as "[HI %Hbound]".
  iApply ("H" with "[$HI //]").
  rewrite adapt_cmp_bounded; [ | lia ].
  done.
Qed.

Lemma wp_Find (n: w64) (cmp_code: func.t) (cmp: Z → Z) (I: iProp Σ) :
  {{{ is_pkg_init sort ∗
      ⌜0 ≤ sint.Z n⌝ ∗
      cmp_implements cmp_code cmp (sint.Z n) I ∗
      I ∗
      ⌜is_mono_cmp cmp (sint.Z n)⌝ }}}
    @! sort.Find #n #cmp_code
  {{{ (i: w64) (found: bool), RET (#i, #found);
      I ∗
      ⌜found = true ↔
        sint.Z i < sint.Z n ∧
        cmp (sint.Z i) = 0⌝ ∗
      ⌜(∀ i, 0 ≤ i < sint.Z n → cmp i > 0) → sint.Z i = sint.Z n⌝ ∗
      ⌜∀ k, 0 ≤ k < sint.Z i → cmp k > 0⌝
  }}}.
Proof using W.
  wp_start as "(%Hpos & #Hcmp0 & I & %Hvalid)".
  wp_auto.

  iDestruct (cmp_implements_adapt with "Hcmp0") as "Hcmp".
  iClear "Hcmp0".
  apply is_valid_cmp_adapted in Hvalid; [ | lia ].

  (* Initialize loop invariant: i = 0, j = n *)
  iAssert (
    ∃ (i j: w64),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "I" ∷ I ∗
      "%Hbounds" ∷ ⌜0 ≤ sint.Z i ≤ sint.Z j ≤ sint.Z n⌝ ∗
      "%Hi_prop" ∷ ⌜adapt_cmp cmp (sint.Z n) (sint.Z i - 1) > 0⌝ ∗
      "%Hj_prop" ∷ ⌜adapt_cmp cmp (sint.Z n) (sint.Z j) ≤ 0⌝
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
      rewrite -> !adapt_cmp_bounded in * by lia.
      split_and!.
      * word.
      * intros Hno_index.
        (* contradiction in the i < n case *)
        pose proof (Hno_index (sint.Z j) ltac:(word)).
        word.
      * intros k Hk.
        destruct Hvalid as (Hmono & Hneg & Hn).
        rewrite -> !adapt_cmp_bounded in * by lia.
        destruct (decide (k = sint.Z i - 1)).
        { subst; word. }
        pose proof (Hmono k (sint.Z i-1) ltac:(word)) as Hmono'.
        rewrite -> !adapt_cmp_bounded in * by lia.
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
        rewrite -> !adapt_cmp_bounded in * by lia.
        destruct (decide (k = sint.Z i - 1)).
        { subst; word. }
        pose proof (Hmono k (sint.Z i-1) ltac:(word)) as Hmono'.
        rewrite -> !adapt_cmp_bounded in * by lia.
        move: Hmono'. rewrite /signum.
        repeat destruct decide; try lia.
Qed.

(* Direct translation of specification text. However, this formulation seems
hard to work with for the common case of a monotonic comparison function, as
you'd get for a sorted list; the relevant lemma is stated below but is hard to
prove. *)
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

Lemma internal_to_real_cmp cmp n :
  0 ≤ n →
  is_valid_cmp cmp n →
  real_valid_cmp cmp n.
Proof.
  intros Hnn (Hmono & Hi & Hj).
  rewrite /real_valid_cmp.
  (* somewhat difficult: need to take a lower bound from a finite interval of
  Z *)
Abort.

End proof.
