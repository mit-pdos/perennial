Require Export New.code.sync.
From New.proof Require Export proof_prelude.
Require Export New.generatedproof.sync.

From New.proof Require Export sync.atomic.
From New.proof Require Export tok_set.

From New.experiments Require Export glob.
From Perennial Require Export base.

Set Default Proof Using "Type".

Inductive rwmutex := RLocked (num_readers : nat) | Locked.

Inductive wlock_state :=
| NotLocked (unnotified_readers : w32)
| SignalingReaders (remaining_readers : w32)
| WaitingForReaders
| IsLocked.

Class syncG Σ := {
    #[global] tokG :: tok_setG Σ;
    #[global] wg_totalG :: ghost_varG Σ w32;

    #[global] rw_ghost_varG :: ghost_varG Σ ();
    #[global] rw_ghost_wlG :: ghost_varG Σ wlock_state;
    #[global] rw_ghost_rwmutexG :: ghost_varG Σ rwmutex;
  }.

Definition syncΣ := #[tok_setΣ; ghost_varΣ w32; ghost_varΣ (); ghost_varΣ wlock_state; ghost_varΣ rwmutex].
Global Instance subG_syncΣ{Σ} : subG (syncΣ) Σ → (syncG Σ).
Proof. solve_inG. Qed.

Section defns.
Context `{heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.
Context `{!syncG Σ}.

#[global]
Program Instance race_pkg_is_init : IsPkgInit race := ltac2:(build_pkg_init ()).

#[global]
Program Instance pkg_is_init : IsPkgInit sync := ltac2:(build_pkg_init ()).

End defns.

Module syncword.
(* FIXME: remove once the real word works well enough *)
Ltac simpl_word_constants :=
  repeat match goal with
         | [ H: context[word.unsigned (W64 ?x)] |- _ ] => change (uint.Z x) with x in H
         | [ |- context[word.unsigned (W64 ?x)] ] => change (uint.Z x) with x
         | [ H: context[word.unsigned (W32 ?x)] |- _ ] => change (uint.Z (W32 x)) with x in H
         | [ |- context[word.unsigned (W32 ?x)] ] => change (uint.Z (W32 x)) with x
         | [ H: context[word.unsigned (W8 ?x)] |- _ ] => change (uint.Z (W8 x)) with x in H
         | [ |- context[word.unsigned (W8 ?x)] ] => change (uint.Z (W8 x)) with x
         | [ H: context[word.signed (W64 ?x)] |- _ ] => change (sint.Z x) with x in H
         | [ |- context[word.signed (W64 ?x)] ] => change (sint.Z x) with x
         | [ H: context[word.signed (W32 ?x)] |- _ ] => change (sint.Z (W32 x)) with x in H
         | [ |- context[word.signed (W32 ?x)] ] => change (sint.Z (W32 x)) with x
         | [ H: context[word.signed (W8 ?x)] |- _ ] => change (sint.Z (W8 x)) with x in H
         | [ |- context[word.signed (W8 ?x)] ] => change (sint.Z (W8 x)) with x
    end.

Lemma word_assume_opposite {width : Z} {word : Interface.word width} {_:word.ok word} (x y : word) :
  (x ≠ y → False) → x = y.
Proof. intros ?. by destruct (decide (x = y)). Qed.

Lemma word_eq_iff {width : Z} {word : Interface.word width} {_:word.ok word} (x y : word) :
  x = y ↔ uint.Z x = uint.Z y.
Proof.
  split; first by intros ->.
  intros ?. by apply (inj uint.Z).
Qed.

Lemma word_eq_iff_signed {width : Z} {word : Interface.word width} {_:word.ok word} (x y : word) :
  x = y ↔ sint.Z x = sint.Z y.
Proof.
  split; first by intros ->.
  intros ?. by apply (inj sint.Z).
Qed.

Ltac word_cleanup_core :=
  unfold w64 in *; unfold w32 in *; unfold w8 in *;
  try (apply word_assume_opposite; intros);
  repeat autounfold with word in *;
  repeat match goal with
         | _ => progress simpl_word_constants
         | [ H: context[@eq (@word.rep _ _) _ _] |- _ ] =>
             (let H' := fresh H "_signed" in
              pose proof H as H'; rewrite word_eq_iff in H; rewrite word_eq_iff_signed in H')
         end;
  (* can't replace some of these with [autorewrite], probably because typeclass inference
  isn't the same *)
  repeat (
      rewrite -> ?word.unsigned_add, ?word.unsigned_sub,
        ?word.unsigned_divu_nowrap, ?word.unsigned_modu_nowrap,
        ?word.unsigned_mul, ?w64_unsigned_ltu,
        ?word.signed_add, ?word.signed_sub in *
      || rewrite -> ?word.unsigned_of_Z, ?word.of_Z_unsigned in *
      || autorewrite with word in *
      || (progress simpl_word_constants)
    );
  fold w64 w32 w8 in *;
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
End syncword.
