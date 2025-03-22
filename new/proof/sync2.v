From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants ghost_map.
From Perennial.program_logic Require Import weakestpre.

Require Export New.code.sync.
From New.proof Require Import proof_prelude.
Require Export New.generatedproof.sync.

From New.proof Require Import sync sync.atomic.
From New.proof Require Import tok_set.
From New.experiments Require Import glob.

From Perennial Require Import base.

Ltac simpl_word_constants :=
  repeat match goal with
         | [ H: context[word.unsigned (W64 ?x)] |- _ ] => change (uint.Z x) with x in H
         | [ |- context[word.unsigned (W64 ?x)] ] => change (uint.Z x) with x
         | [ H: context[word.unsigned (W32 ?x)] |- _ ] => change (uint.Z (W32 x)) with x in H
         | [ |- context[word.unsigned (W32 ?x)] ] => change (uint.Z (W32 x)) with x
         | [ H: context[word.unsigned (W8 ?x)] |- _ ] => change (uint.Z (W32 8)) with x in H
         | [ |- context[word.unsigned (W8 ?x)] ] => change (uint.Z (W8 x)) with x
         | [ H: context[word.signed (W64 ?x)] |- _ ] => change (sint.Z x) with x in H
         | [ |- context[word.signed (W64 ?x)] ] => change (sint.Z x) with x
         | [ H: context[word.signed (W32 ?x)] |- _ ] => change (sint.Z (W32 x)) with x in H
         | [ |- context[word.signed (W32 ?x)] ] => change (sint.Z (W32 x)) with x
         | [ H: context[word.signed (W8 ?x)] |- _ ] => change (sint.Z (W32 8)) with x in H
         | [ |- context[word.signed (W8 ?x)] ] => change (sint.Z (W8 x)) with x
        (* TODO: add sint versions *)
    end.

Ltac word_cleanup_core :=
  (* this is so that the following pattern succeeds when (for some reason)
  instead of w64 we have its unfolding *)
  fold w64 w32 w8 in *;
  repeat autounfold with word in *;
  try lazymatch goal with
      (* TODO: this isn't the right strategy if the numbers in the goal are used
      signed. [word] can try both via backtracking, but this can't be part of
      "cleanup".  *)
      | |- @eq u64 _ _ => apply word.unsigned_inj
      | |- @eq u32 _ _ => apply word.unsigned_inj
      | |- @eq u8 _ _ => apply word.unsigned_inj
      | |- not (@eq u64 _ _) => apply (f_not_equal uint.Z)
      | |- not (@eq u32 _ _) => apply (f_not_equal uint.Z)
      | |- not (@eq u8 _ _) => apply (f_not_equal uint.Z)
      end;
  simpl_word_constants;
  (* can't replace some of these with [autorewrite], probably because typeclass inference
  isn't the same *)
  repeat (
      rewrite -> ?word.unsigned_add, ?word.unsigned_sub,
        ?word.unsigned_divu_nowrap, ?word.unsigned_modu_nowrap,
        ?word.unsigned_mul, ?w64_unsigned_ltu,
        ?word.signed_add, ?word.signed_sub in *
      || rewrite -> ?word.unsigned_of_Z, ?word.of_Z_unsigned in *
      || autorewrite with word in *
    );
  repeat match goal with
         | _ => progress simpl_word_constants
         | [ H: @eq w64 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w64_val_f_equal in H as [H H']
         | [ H: @eq w32 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w32_val_f_equal in H as [H H']
         | [ H: not (@eq w64 _ _) |- _ ] => let H' := fresh H "_signed" in
                                      apply w64_val_neq in H as [H H']
         | [ H: @eq w32 _ _ |- _ ] => let H' := fresh H "_signed" in
                                      apply w32_val_neq in H as [H H']
         end;
  repeat match goal with
         | [ |- context[uint.Z ?x] ] =>
           lazymatch goal with
           | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.unsigned_range x)
           end
         | [ H: context[uint.Z ?x] |- _ ] =>
           lazymatch goal with
           | [ H': 0 <= uint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.unsigned_range x)
           end
         | [ |- context[sint.Z ?x] ] =>
           lazymatch goal with
           | [ H': - (2^ _) ≤ sint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.signed_range x)
           end
         | [ H: context[sint.Z ?x] |- _ ] =>
           lazymatch goal with
           | [ H': - (2^ _) ≤ sint.Z x < 2^_ |- _ ] => fail
           | _ => pose proof (word.signed_range x)
           end
         end;
  repeat match goal with
         | |- context[@word.wrap _ ?word ?ok ?z] =>
           rewrite -> (@wrap_small _ word ok z) by lia
         | |- context[@word.swrap _ ?word ?ok ?z] =>
           rewrite -> (@swrap_small _ word ok z) by lia
         | |- context[Z.of_nat (Z.to_nat ?z)] =>
           rewrite -> (Z2Nat.id z) by lia
         end.

(* TODO: only for backwards compatibility.

[word_cleanup] should be be replaced with a new tactic
that does a subset of safe and useful rewrites *)
Ltac word_cleanup := word_cleanup_core; try lia.

Ltac word := first [
                 solve [
                     try iPureIntro;
                     word_cleanup_core;
                     unfold word.wrap in *;
                     unfold word.swrap in *;
                     (* NOTE: some inefficiency here because [lia] will do [zify]
                 again, but we can't rebind the zify hooks in Ltac *)
                     zify; Z.div_mod_to_equations; lia
                   ]
               | fail 1 "word could not solve goal"
               ].

(* TODO: use for first abstraction. *)
Local Definition enc (low high : w32) : w64 :=
  word.add (word.slu (W64 (uint.Z high)) (W64 32)) (W64 (uint.Z low)).

(* TODO: use for first abstraction. *)
Local Ltac local_word :=
  try apply word.unsigned_inj;
  repeat try (
      rewrite !word.unsigned_sru // in * ||
      rewrite word.unsigned_add ||
      rewrite word.unsigned_slu // ||
      rewrite !Z.shiftr_div_pow2 // ||
      rewrite Z.shiftl_mul_pow2 //
    ); word.

(* TODO: this is an abstraction of the physical state. *)
Record Impl := mkImpl { v : w32; w : w32; sema : u32; }.
Global Instance settable : Settable _ :=
  settable! mkImpl < v; w; sema >.
Implicit Types s : Impl.

Inductive ImplStep :=
| Add1 (delta : w32) | Add2 | Add3
| Wait1 (oldv oldw : w32) | Wait2.

Implicit Type (l : ImplStep).

Definition step_impl l s s' : Prop :=
  match l with
  | Add1 delta => (s' = s <| v := word.add s.(v) delta |>)
  | Add2 => (s' = s <| v := W32 0 |> <| w := W32 0 |>)
  | Add3 => (s' = s <| sema := (word.add s.(sema) (W32 1)) |>)

  | Wait1 oldv oldw => if decide (s.(v) = oldv ∧ s.(w) = oldw) then
                        (s' = s <| w := (word.add oldw (W32 1)) |>)
                      else s' = s
  | Wait2 => (0 < uint.Z s.(sema)) ∧ (s' = s <| sema := word.sub s.(sema) (W32 1) |>)
  end.

Record Spec := { counter : w32; }.
Implicit Types t : Spec.

Inductive SpecStep := Add (delta : w32) | Wait.
Implicit Type (m : SpecStep).

Definition step_spec m t t' : Prop :=
  match m with
  | Add delta => t'.(counter) = word.add t.(counter) delta
  | Wait => t' = t ∧ t.(counter) = W32 0
  end.

Inductive AuxAdd := AddNot | AddNeedToSignal.
Implicit Types a : AuxAdd.
Definition next_add_aux l s s' a : AuxAdd :=
  match l with
  | Add1 _ => if decide (s'.(v) = W32 0) then AddNeedToSignal else AddNot
  | _ => AddNot
  end.

Definition invariant s t a : Prop :=
  t.(counter) = s.(v) ∧ (* abstraction *)
  match a with
  | AddNeedToSignal => s.(v) = W32 0
  | _ => True
  end.

Lemma impl_invariant_Add1 delta s s' t a :
  0 ≤ sint.Z t.(counter) + sint.Z delta < 2^31 →
  step_impl (Add1 delta) s s' →
  invariant s t a →
  ∃ t', step_spec (Add delta) t t' ∧ invariant s' t' (next_add_aux (Add1 delta) s s' a).
Proof.
  intros Hpre Hstep Hinv. destruct s as [v w sema], s' as [v' w' sema'], t as [counter].
  exists {|sync2.counter := v'|}. unfold invariant in *. simpl in *.
  unfold set in Hstep. simplify_eq. intuition; try word. by destruct decide.
Qed.

Lemma impl_invariant_Add2 s s' t a :
  (* XXX: The precondition here is actually meant to denote ownership. *)
  a = AddNeedToSignal →
  step_impl Add2 s s' →
  invariant s t a →
  invariant s' t (next_add_aux (Add2) s s' a).
Proof.
  intros -> Hstep Hinv. destruct s as [v w sema], s' as [v' w' sema'], t as [counter].
  unfold invariant in *. simpl in *. unfold set in *. simpl in *. simplify_eq.
  intuition; subst; done.
Qed.

Lemma impl_invariant_Add3 s s' t a :
  step_impl Add3 s s' →
  invariant s t a →
  invariant s' t (next_add_aux (Add3) s s' a).
Proof.
  intros Hstep Hinv. destruct s as [v w sema], s' as [v' w' sema'], t as [counter].
  unfold invariant in *. simpl in *. unfold set in *. simpl in *. simplify_eq.
  intuition; subst; done.
Qed.

Lemma impl_invariant_Wait1 oldv oldw s s' t a :
  sint.Z oldv ≠ 0 →
  step_impl (Wait1 oldv oldw) s s' →
  invariant s t a →
  invariant s' t (next_add_aux (Wait1 oldv oldw) s s' a).
Proof.
  intros Hstep Hinv. destruct s as [v w sema], s' as [v' w' sema'], t as [counter].
  unfold invariant in *. simpl in *.
  unfold set in *. simpl in *. destruct decide; simplify_eq.
  all: intuition; subst; done.
Qed.

Lemma impl_invariant_Wait2 s s' t a :
  step_impl Wait2 s s' →
  invariant s t a →
  ∃ t', step_spec Wait t t' ∧
        invariant s' t' (next_add_aux Wait2 s s' a).
Proof.
  intros Hstep Hinv. exists t. destruct s as [v w sema], s' as [v' w' sema'], t as [counter].
  unfold invariant in *. simpl in *.
  unfold set in *. simpl in *. destruct Hstep as [? Hstep].
  simplify_eq. split_and!; try done.
  {
Abort.
(* Need invariant to imply that counter = 0 in this case. But, that's not enough:
   need to walk away with a fact that says the counter will remain zero until
   the Wait() call returns.
   I.e. want some sort of ownership. *)


(* Q: steps are constrained by preconditions on API functions. How does that show up here? *)
Lemma invariant_impl_step s s' a :
  precondition t
  abstraction s t →
  step_impl s s' → invariant_impl s a → invariant_impl s' (next_add_aux s s' a).
Proof.
  destruct s, s'.
  intros Hstep Hinv.
  destruct Hstep.
  {
    simpl in *. subst.
    unfold invariant_impl in *.
    intros ?.
  }
Qed.
