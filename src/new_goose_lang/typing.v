From Perennial.goose_lang Require Import lang notation.

Section val_types.
  Inductive go_type :=
  (* Boolean *)
  | boolT

  (* Numeric, except float and impl-specific sized objects *)
  | uint8T
  | uint16T
  | uint32T
  | uint64T
  | int8T
  | int16T
  | int32T
  | int64T

  | stringT
  (* | arrayT (len : nat) (elem : go_type) *)
  | sliceT (elem : go_type)
  | structT (decls : list (string * go_type)) (* What if this were a gmap? *)
  | ptrT (* Untyped pointer; convenient to support recursion in structs *)
  | funcT
  | interfaceT
  | mapT (key elem : go_type)
  | chanT (elem : go_type)
  .
  Definition byteT := uint8T.

  Context `{ffi_syntax}.
  Definition nil : val := #null.
  Definition slice_nil : val := (nil, nil, nil).
  Definition interface_nil : val := (nil, nil, nil).
  Fixpoint zero_val (t : go_type) : val :=
    match t with
    | boolT => #false

    (* Numeric, except float and impl-specific sized objects *)
    | uint8T => #(W8 0)
    | uint16T => nil
    | uint32T => #(W32 0)
    | uint64T => #(W64 0)
    | int8T => #(W8 0)
    | int16T => nil
    | int32T => #(W32 0)
    | int64T => #(W64 0)

    | stringT => #(str "")
    (* | arrayT (len : nat) (elem : go_type) *)
    | sliceT _ => slice_nil
    | structT decls => fold_right PairV #() (fmap (zero_val ∘ snd) decls)
    | ptrT => nil
    | funcT => nil
    | interfaceT => interface_nil
    | mapT _ _ => nil
    | chanT _ => nil
    end
  .

  (* The below is not in the TCB. It's there so the proof can work (entirely)
     with Coq-typed objects. *)
  Class IntoValTyped V (t:go_type) :=
    {
      to_val : V → val ;
      IntoValTyped_def : V ;
      IntoValTyped_def_zero : zero_val t = to_val IntoValTyped_def ;
      IntoValTyped_inj : Inj eq eq to_val ;
    }.

  Global Hint Mode IntoValTyped - ! : typeclass_instances.
  Global Hint Mode IntoValTyped ! - : typeclass_instances.
  Notation "≀ x" := (to_val x) (at level 20, format "≀ x").

  Program Global Instance u64_IntoVal_uint64T : IntoValTyped w64 uint64T :=
    {
      to_val v := LitV v ;
      IntoValTyped_def := W64 0 ;
      IntoValTyped_def_zero := eq_refl ;
    }.
  Obligation 1. intros ???. by injection H0. Qed.

  Opaque to_val.
  Opaque zero_val.
  (*
  Eval simpl in (zero_val uint64T).
  Eval simpl in (# (IntoValTyped_def u64 uint64T)).
  Eval simpl in (to_val (IntoValTyped_def u64 uint64T)). *)

End val_types.
