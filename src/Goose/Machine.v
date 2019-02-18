From Coq Require Import ProofIrrelevance.
From Coq Require Export String.

From Classes Require Import EqualDec.
From RecordUpdate Require Import RecordUpdate.

From stdpp Require Import decidable countable.
From stdpp Require gmap.
From stdpp Require Import fin_maps.

Set Implicit Arguments.

Instance eqdecision `{dec:EqualDec A} : EqDecision A := dec.

(*! Basic datatypes *)

Definition uint64 := nat.

Definition compare_to x y (c: comparison)
  : {match c with
     | Lt => x < y
     | Gt => y < x
     | Eq => x = y
     end} +
    {match c with
     | Lt => x >= y
     | Gt => y >= x
     | Eq => x <> y
     end}.
  destruct c.
  - apply Nat.eq_dec.
  - destruct (lt_dec x y); auto; right; abstract omega.
  - destruct (lt_dec y x); auto; right; abstract omega.
Defined.

Axiom byte:Type.
Axiom byte0:byte.

(*! Pure model of uint64 little-endian encoding. *)

Record LittleEndianEncoder bytes intTy (enc:intTy -> list byte) (dec:list byte -> option intTy) :=
  { encode_length_ok : forall x, length (enc x) = bytes;
    encode_decode_ok : forall x, dec (enc x) = Some x; }.

Axiom uint64_to_le : uint64 -> list byte.
Axiom uint64_from_le : list byte -> option uint64.
Axiom uint64_le_enc : LittleEndianEncoder 8 uint64_to_le uint64_from_le.

(*! File descriptors *)
(* note these are Go file handles, which may be nil *)
Axiom File : Type.
Axiom nilFile : File.
Declare Instance file_eqdec : EqualDec File.
Declare Instance file_countable : Countable File.

(*! Pointers *)

Module Ptr.
  Inductive ty : Type :=
  | Heap (T:Type)
  | Map (V:Type)
  | Lock
  .

  Axiom t : ty -> Type.
End Ptr.

Axiom nullptr : forall ty, Ptr.t ty.

Definition ptr T := Ptr.t (Ptr.Heap T).
Definition Map V := Ptr.t (Ptr.Map V).
Definition LockRef := Ptr.t Ptr.Lock.

Declare Instance sigPtr_eq_dec : EqualDec (sigT Ptr.t).

Module slice.
  Section Slices.
    Variable A:Type.

    Record t :=
      mk { ptr: Ptr.t (Ptr.Heap A);
           offset: uint64;
           length: uint64 }.

    Instance _eta : Settable t :=
      mkSettable (constructor mk <*> ptr <*> offset <*> length)%set.

    Definition nil := {| ptr := nullptr _; offset := 0; length := 0 |}.

    Definition skip (n:uint64) (x:t) : t :=
      set length (fun l => l - n)
          (set offset (fun o => o + n) x).

    Definition take (n:uint64) (x:t) : t :=
      set length (fun _ => n) x.

    Definition subslice (low high:uint64) (x:t) : t :=
      set length (fun _ => high - low)
          (set offset (fun o => o + low) x).

    Theorem subslice_skip_take low high x :
      subslice low high x = skip low (take high x).
    Proof.
      destruct x; unfold subslice, skip; simpl; auto.
    Qed.

    Theorem subslice_take_skip low high x :
      subslice low high x = take (high - low) (skip low x).
    Proof.
      destruct x; unfold subslice, skip; simpl; auto.
    Qed.
  End Slices.
End slice.

Instance slice_eq_dec : EqualDec (sigT slice.t).
Proof.
  hnf; intros.
  destruct x as [T1 x], y as [T2 y].
  destruct x, y; simpl.
  destruct (equal (existT _ ptr0) (existT _ ptr1));
    [ | right ].
  - destruct (equal offset offset0), (equal length length0);
      [ left | right.. ];
      repeat match goal with
             | [ H: existT ?T _ = existT ?T _ |- _ ] =>
               apply inj_pair2 in H; subst
             | [ H: existT _ _ = existT _ _ |- _ ] =>
               inversion H; subst; clear H
             end; eauto; try (inversion 1; congruence).
  - inversion 1; subst.
    apply inj_pair2 in H2; subst; congruence.
Defined.
