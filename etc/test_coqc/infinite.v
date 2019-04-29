(* Copyright (c) 2012-2019, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Export list.
From stdpp Require Import relations pretty.

(** * Generic constructions *)
(** If [A] is infinite, and there is an injection from [A] to [B], then [B] is
also infinite. Note that due to constructivity we need a rather strong notion of
being injective, we also need a partial function [B → option A] back. *)
Program Definition inj_infinite `{Infinite A} {B}
    (f : A → B) (g : B → option A) (Hgf : ∀ x, g (f x) = Some x) :
  Infinite B := {| infinite_fresh := f ∘ fresh ∘ omap g |}.
Next Obligation.
  intros A ? B f g Hfg xs Hxs; simpl in *.
  apply (infinite_is_fresh (omap g xs)), elem_of_list_omap; eauto.
Qed.
Next Obligation. solve_proper. Qed.

(** If there is an injective function [f : nat → B], then [B] is infinite. This
construction works as follows: to obtain an element not in [xs], we return the
first element [f 0], [f 1], [f 2], ... that is not in [xs].

This construction has a nice computational behavior to e.g. find fresh strings.
Given some prefix [s], we use [f n := if n is S n' then s +:+ pretty n else s].
The construction then finds the first string starting with [s] followed by a
number that's not in the input list. For example, given [["H", "H1", "H4"]] and
[s := "H"], it would find ["H2"]. *)
Section search_infinite.
  Context {B} (f : nat → B) `{!Inj (=) (=) f, !EqDecision B}.

  Let R (xs : list B) (n1 n2 : nat) :=
    n2 < n1 ∧ (f (n1 - 1)) ∈ xs.
  Lemma search_infinite_step xs n : f n ∈ xs → R xs (1 + n) n.
  Proof. split; [lia|]. replace (1 + n - 1) with n by lia; eauto. Qed.
  Lemma search_infinite_R_wf xs : wf (R xs).
  Proof.
    revert xs. assert (help : ∀ xs n n',
      Acc (R (filter (≠ f n') xs)) n → n' < n → Acc (R xs) n).
    { induction 1 as [n _ IH]. constructor; intros n2 [??]. apply IH; [|lia].
      split; [done|]. apply elem_of_list_filter; naive_solver lia. }
    intros xs. induction (well_founded_ltof _ length xs) as [xs _ IH].
    intros n1; constructor; intros n2 [Hn Hs].
    apply help with (n2 - 1); [|lia]. apply IH. eapply filter_length_lt; eauto.
  Qed.

  Definition search_infinite_go (xs : list B) (n : nat)
      (go : ∀ n', R xs n' n → B) : B :=
    let x := f n in
    match decide (x ∈ xs) with
    | left Hx => go (S n) (search_infinite_step xs n Hx)
    | right _ => x
    end.

  Program Definition search_infinite : Infinite B := {|
    infinite_fresh xs :=
      Fix_F _ (search_infinite_go xs) (wf_guard 32 (search_infinite_R_wf xs) 0)
  |}.
  Next Obligation.
    intros xs. unfold fresh.
    generalize 0 (wf_guard 32 (search_infinite_R_wf xs) 0). revert xs.
    fix FIX 3; intros xs n [?]; simpl; unfold search_infinite_go at 1; simpl.
    destruct (decide _); auto.
  Qed.
  Next Obligation.
    intros xs1 xs2 Hxs. unfold fresh.
    generalize (wf_guard 32 (search_infinite_R_wf xs1) 0).
    generalize (wf_guard 32 (search_infinite_R_wf xs2) 0). generalize 0.
    fix FIX 2. intros n [acc1] [acc2]; simpl; unfold search_infinite_go.
    destruct (decide ( _ ∈ xs1)) as [H1|H1], (decide (_ ∈ xs2)) as [H2|H2]; auto.
    - destruct H2. by rewrite <-Hxs.
    - destruct H1. by rewrite Hxs.
  Qed.
End search_infinite.

(** To select a fresh number from a given list [x₀ ... xₙ], a possible approach
is to compute [(S x₀) `max` ... `max` (S xₙ) `max` 0]. For non-empty lists of
non-negative numbers this is equal to taking the maximal element [xᵢ] and adding
one.

The construction below generalizes this construction to any type [A], function
[f : A → A → A]. and initial value [a]. The fresh element is computed as
[x₀ `f` ... `f` xₙ `f` a]. For numbers, the prototypical instance is
[f x y := S x `max` y] and [a:=0], which gives the behavior described before.
Note that this gives [a] (i.e. [0] for numbers) for the empty list. *)
Section max_infinite.
  Context {A} (f : A → A → A) (a : A) (lt : relation A).
  Context (HR : ∀ x, ¬lt x x).
  Context (HR1 : ∀ x y, lt x (f x y)).
  Context (HR2 : ∀ x x' y, lt x x' → lt x (f y x')).
  Context (Hf : ∀ x x' y, f x (f x' y) = f x' (f x y)).

  Program Definition max_infinite: Infinite A := {|
    infinite_fresh := foldr f a
  |}.
  Next Obligation.
    cut (∀ xs x, x ∈ xs → lt x (foldr f a xs)).
    { intros help xs []%help%HR. }
    induction 1; simpl; auto.
  Qed.
  Next Obligation. by apply (foldr_permutation_proper _ _ _). Qed.
End max_infinite.

(** Instances for number types *)
Program Instance nat_infinite : Infinite nat :=
  max_infinite (Nat.max ∘ S) 0 (<) _ _ _ _.
Solve Obligations with (intros; simpl; lia).

Program Instance N_infinite : Infinite N :=
  max_infinite (N.max ∘ N.succ) 0%N N.lt _ _ _ _.
Solve Obligations with (intros; simpl; lia).

Program Instance positive_infinite : Infinite positive :=
  max_infinite (Pos.max ∘ Pos.succ) 1%positive Pos.lt _ _ _ _.
Solve Obligations with (intros; simpl; lia).

Program Instance Z_infinite: Infinite Z :=
  max_infinite (Z.max ∘ Z.succ) 0%Z Z.lt _ _ _ _.
Solve Obligations with (intros; simpl; lia).

(** Instances for option, sum, products *)
Instance option_infinite `{Infinite A} : Infinite (option A) :=
  inj_infinite Some id (λ _, eq_refl).

Instance sum_infinite_l `{Infinite A} {B} : Infinite (A + B) :=
  inj_infinite inl (maybe inl) (λ _, eq_refl).
Instance sum_infinite_r {A} `{Infinite B} : Infinite (A + B) :=
  inj_infinite inr (maybe inr)  (λ _, eq_refl).

Instance prod_infinite_l `{Infinite A, Inhabited B} : Infinite (A * B) :=
  inj_infinite (,inhabitant) (Some ∘ fst) (λ _, eq_refl).
Instance prod_infinite_r `{Inhabited A, Infinite B} : Infinite (A * B) :=
  inj_infinite (inhabitant,) (Some ∘ snd) (λ _, eq_refl).

(** Instance for lists *)
Program Instance list_infinite `{Inhabited A} : Infinite (list A) := {|
  infinite_fresh xxs := replicate (fresh (length <$> xxs)) inhabitant
|}.
Next Obligation.
  intros A ? xs ?. destruct (infinite_is_fresh (length <$> xs)).
  apply elem_of_list_fmap. eexists; split; [|done].
  unfold fresh. by rewrite replicate_length.
Qed.
Next Obligation. unfold fresh. by intros A ? xs1 xs2 ->. Qed.

(** Instance for strings *)
Program Instance string_infinite : Infinite string :=
  search_infinite pretty.
