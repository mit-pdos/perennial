From Perennial.goose_lang Require Export lang notation.

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
  Definition slice_nil : val := (nil, #0, #0).
  Definition interface_nil : val := (nil, nil, nil).
  Fixpoint zero_val_def (t : go_type) : val :=
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
    | structT decls => fold_right PairV #() (fmap (zero_val_def ∘ snd) decls)
    | ptrT => nil
    | funcT => nil
    | interfaceT => interface_nil
    | mapT _ _ => nil
    | chanT _ => nil
    end.
Program Definition zero_val := unseal (_:seal (@zero_val_def)). Obligation 1. by eexists. Qed.
Definition zero_val_unseal : zero_val = _ := seal_eq _.

Fixpoint go_type_size_def (t : go_type) : nat :=
  match t with
  | structT d =>
      (fix go_type_size_struct d : nat :=
        match d with
        | [] => O
        | (_,t) :: d => (go_type_size_def t + go_type_size_struct d)%nat
        end
      ) d
  | sliceT e => 3
  | interfaceT => 3
  | _ => 1
  end.
Program Definition go_type_size := unseal (_:seal (@go_type_size_def)). Obligation 1. by eexists. Qed.
Definition go_type_size_unseal : go_type_size = _ := seal_eq _.
End val_types.

Reserved Notation "l +ₗ[ t ] z" (at level 50, left associativity, format "l  +ₗ[ t ]  z").
Notation "l +ₗ[ t ] z" := (l +ₗ go_type_size t * z) : stdpp_scope .
Notation "e1 +ₗ[ t ] e2" := (BinOp (OffsetOp (go_type_size t)) e1%E e2%E) : expr_scope .

Fixpoint assocl_lookup {A} (field_vals: list (string * A)) (f0: string) : option A :=
  match field_vals with
  | [] => None
  | (f, v)::fs => if String.eqb f f0 then Some v else assocl_lookup fs f0
  end.

Module struct.
  Definition descriptor := list (string * go_type).
End struct.
