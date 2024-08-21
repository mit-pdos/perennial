From Perennial.goose_lang Require Export lang notation.
From New.golang.defn Require Export list.

Module array.
Section defn.
  Context `{ffi_syntax}.
  Fixpoint val_def (x : list val) : val :=
    match x with
    | [] => #()
    | h :: tl => (h, val_def tl)
    end
  .
  Program Definition val := unseal (_:seal (@val_def)). Obligation 1. by eexists. Qed.
  Definition val_unseal : val = _ := seal_eq _.
End defn.
End array.

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
  | arrayT (n : nat) (elem : go_type)
  | sliceT (elem : go_type)
  | structT (decls : list (string * go_type)) (* What if this were a gmap? *)
  | ptrT (* Untyped pointer; convenient to support recursion in structs *)
  | funcT
  | interfaceT
  | mapT (key elem : go_type)
  | chanT (elem : go_type)
  .

  (* This type is never supposed to be used in real code; if you're ever forced
     to deal with it in a proof, then something in Goose must have gone
     wrong. *)
  Definition badT_def := ptrT.
  Program Definition badT := unseal (_:seal (@badT_def)). Obligation 1. by eexists. Qed.
  Definition badT_unseal : badT = _ := seal_eq _.

  Definition byteT := uint8T.
  Definition intT := int64T.

  Context `{ffi_syntax}.
  Definition go_nil : val := #null.
  Definition slice_nil : val := (go_nil, #0, #0).
  Definition interface_nil : val := (go_nil, go_nil, go_nil).
  Fixpoint zero_val_def (t : go_type) : val :=
    match t with
    | boolT => #false

    (* Numeric, except float and impl-specific sized objects *)
    | uint8T => #(W8 0)
    | uint16T => go_nil
    | uint32T => #(W32 0)
    | uint64T => #(W64 0)
    | int8T => #(W8 0)
    | int16T => go_nil
    | int32T => #(W32 0)
    | int64T => #(W64 0)

    | stringT => #(str "")
    | arrayT n elem => array.val (replicate n (zero_val_def elem))
    | sliceT _ => slice_nil
    | structT decls => fold_right PairV #() (fmap (zero_val_def ∘ snd) decls)
    | ptrT => go_nil
    | funcT => go_nil
    | interfaceT => interface_nil
    | mapT _ _ => go_nil
    | chanT _ => go_nil
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
    | arrayT n e => n * (go_type_size_def e)
    | _ => 1
    end.
  Program Definition go_type_size := unseal (_:seal (@go_type_size_def)). Obligation 1. by eexists. Qed.
  Definition go_type_size_unseal : go_type_size = _ := seal_eq _.
End val_types.

Reserved Notation "l +ₗ[ t ] z" (at level 50, left associativity, format "l  +ₗ[ t ]  z").
Notation "l +ₗ[ t ] z" := (l +ₗ go_type_size t * z) : stdpp_scope .
Notation "e1 +ₗ[ t ] e2" := (BinOp (OffsetOp (go_type_size t)) e1%E e2%E) : expr_scope .

Fixpoint assocl_lookup {A} (f : string) (field_vals: list (string * A)) : option A :=
  match field_vals with
  | [] => None
  | (f', v)::fs => if String.eqb f' f then Some v else assocl_lookup f fs
  end.

Module struct.
  Definition descriptor := list (string * go_type).

Section goose_lang.
  Context `{ffi_syntax}.

  Definition fields_val_def (m : list (string* val)) : val :=
    list.val (fmap (λ '(a,b), (#(str a), b)%V) m).
  Program Definition fields_val := unseal (_:seal (@fields_val_def)). Obligation 1. by eexists. Qed.
  Definition fields_val_unseal : fields_val = _ := seal_eq _.
End goose_lang.
End struct.
