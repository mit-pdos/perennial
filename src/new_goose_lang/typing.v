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
  | chanT (elem : go_type).

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
    end.

End val_types.
