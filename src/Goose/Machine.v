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

Record FixedLengthEncoder bytes intTy byteTy (enc:intTy -> list byteTy) (dec:list byteTy -> option intTy) :=
  { encode_length_ok : forall x, length (enc x) = bytes;
    encode_decode_ok : forall x, dec (enc x) = Some x; }.

Module Ptr.
  Inductive ty : Type :=
  | Heap (T:Type)
  | Map (V:Type)
  | Lock
  .
End Ptr.

Class GoModel : Type :=
  { byte : Type;
    byte0 : byte;

    (*! Strings *)
    uint64_to_string : uint64 -> string;
    ascii_to_byte : Ascii.ascii -> byte;
    byte_to_ascii : byte -> Ascii.ascii;

    (*! Pure model of uint64 little-endian encoding. *)
    uint64_to_le : uint64 -> list byte;
    uint64_from_le : list byte -> option uint64;

    (*! File handles *)
    File : Type;
    (* TODO: rename this, its should be an invalid fd (unfortunately its the
    zero value for File, which is the valid Fd 0) *)
    nilFile : File;

    (*! Pointers *)
    Ptr : Ptr.ty -> Type;
    nullptr : forall ty, Ptr ty;


  }.

Class GoModelWf (model:GoModel) :=
  { uint64_to_string_inj :
      forall x y, uint64_to_string x = uint64_to_string y -> x = y;
    ascii_byte_bijection1 : forall c, byte_to_ascii (ascii_to_byte c) = c;
    ascii_byte_bijection2 : forall b, ascii_to_byte (byte_to_ascii b) = b;
    uint64_le_enc : FixedLengthEncoder 8 uint64_to_le uint64_from_le;
    file_eqdec :> EqualDec File;
    file_countable :> Countable File;
    sigPtr_eq_dec :> EqualDec (sigT Ptr);
  }.

Section DerivedMethods.
  Context {model:GoModel} {model_wf:GoModelWf model}.

  Fixpoint bytes_to_string (l: list byte) : string :=
    match l with
    | nil => EmptyString
    | b::bs => String (byte_to_ascii b) (bytes_to_string bs)
    end.

  Fixpoint string_to_bytes (s: string) : list byte :=
    match s with
    | EmptyString => nil
    | String c s' => ascii_to_byte c :: string_to_bytes s'
    end.

  Theorem bytes_to_string_bijection_1 : forall l,
      string_to_bytes (bytes_to_string l) = l.
  Proof.
    induction l; simpl;
      rewrite ?ascii_byte_bijection1, ?ascii_byte_bijection2; congruence.
  Qed.

  Theorem bytes_to_string_bijection_2 : forall s,
      bytes_to_string (string_to_bytes s) = s.
  Proof.
    induction s; simpl;
      rewrite ?ascii_byte_bijection1, ?ascii_byte_bijection2; congruence.
  Qed.

  Definition ptr T := Ptr (Ptr.Heap T).
  Definition Map V := Ptr (Ptr.Map V).
  Definition LockRef := Ptr Ptr.Lock.

End DerivedMethods.

Module slice.
  Section Slices.
    Context {model:GoModel}.
    Variable A:Type.

    Record t :=
      mk { ptr: Ptr (Ptr.Heap A);
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

Instance slice_eq_dec `{GoModelWf} : EqualDec (sigT slice.t).
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
    apply inj_pair2 in H3; subst; congruence.
Defined.
