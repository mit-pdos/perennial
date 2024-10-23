From Perennial.goose_lang Require Export lang notation.

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
| sliceT
| interfaceT
| structT (decls : list (string * go_type)) (* What if this were a gmap? *)
| ptrT (* Untyped pointer; convenient to support recursion in structs *)
| funcT
| mapT (key elem : go_type)
| chanT (elem : go_type)
.

Class IntoVal `{ffi_syntax} (V : Type) :=
  {
    to_val_def : V → val;
  }.

Program Definition to_val := unseal (_:seal (@to_val_def)). Obligation 1. by eexists. Qed.
Definition to_val_unseal : to_val = _ := seal_eq _.
Arguments to_val {_ _ _} v.
(* Disable Notation "# l". *)
Global Notation "# x" := (to_val x).
Global Notation "#" := to_val.

(* One of [V] or [ty] should not be an evar before doing typeclass search *)
Global Hint Mode IntoVal - ! : typeclass_instances.

Module func.
Section defn.
Context `{ffi_syntax}.
Record t := mk {
      f : binder;
      x : binder;
      e : expr;
    }.
Definition nil := mk <> <> (LitV LitPoison).
End defn.
End func.

Section primitive_instances.
Context `{ffi_syntax}.

Global Instance into_val_loc : IntoVal loc :=
  {| to_val_def := λ v, (LitV $ LitLoc v) |}.

Global Instance into_val_w64 : IntoVal w64 :=
  {| to_val_def := λ v, (LitV $ LitInt v) |}.

Global Instance into_val_w32 : IntoVal w32 :=
  {| to_val_def := λ v, (LitV $ LitInt32 v) |}.

Global Instance into_val_w8 : IntoVal w8 :=
  {| to_val_def := λ v, (LitV $ LitByte v) |}.

Global Instance into_val_unit : IntoVal () :=
  {| to_val_def := λ _, (LitV $ LitUnit) |}.

Global Instance into_val_bool : IntoVal bool :=
  {| to_val_def := λ b, (LitV $ LitBool b) |}.

Global Instance into_val_string : IntoVal string :=
  {| to_val_def := λ s, (LitV $ LitString s) |}.

Global Instance into_val_func : IntoVal func.t :=
  {| to_val_def := λ (f : func.t), RecV f.(func.f) f.(func.x) f.(func.e) |}.
End primitive_instances.

Module slice.
Record t := mk { ptr_f: loc; len_f: u64; cap_f: u64; }.
Definition nil : slice.t := mk null 0 0.
End slice.

Module interface.
Section goose_lang.
  Context `{ffi_syntax}.
  Record t := mk { v: val; mset: list (string * val) }.

  (* FIXME: use the typeid to distinguish nil interface value from nil pointer
     used as a non-nil interface value. *)
  Definition nil := mk #null [].
End goose_lang.
End interface.

Fixpoint assocl_lookup {A} (f : string) (field_vals: list (string * A)) : option A :=
  match field_vals with
  | [] => None
  | (f', v)::fs => if String.eqb f' f then Some v else assocl_lookup f fs
  end.

Module list.
Section defn.
  Context `{ffi_syntax}.
  Fixpoint val_def (x : list val) : val :=
    match x with
    | [] => InjLV #()
    | h :: tl => (InjRV (h, val_def tl))
    end.
  Program Definition val := unseal (_:seal (@val_def)). Obligation 1. by eexists. Qed.
  Definition val_unseal : val = _ := seal_eq _.
End defn.
End list.

Module struct.
Definition descriptor := list (string * go_type).
Section goose_lang.
  Context `{ffi_syntax}.

  Definition fields_val_def (m : list (string* val)) : val :=
    list.val (fmap (λ '(a,b), (#a, b)%V) m).
  Program Definition fields_val := unseal (_:seal (@fields_val_def)). Obligation 1. by eexists. Qed.
  Definition fields_val_unseal : fields_val = _ := seal_eq _.
End goose_lang.
End struct.

Section instances.
Context `{ffi_syntax}.
Global Instance into_val_array `{!IntoVal V} : IntoVal (list V) :=
  {| to_val_def :=
      fix go (x : list V) : val :=
        match x with
        | [] => #()
        | h :: tl => (#h, go tl)%V
        end
  |}.

Global Instance into_val_slice : IntoVal slice.t :=
  {|
    to_val_def (s: slice.t) := InjLV (#s.(slice.ptr_f), #s.(slice.len_f), #s.(slice.cap_f))
  |}.

Global Instance slice_eq_dec : EqDecision slice.t.
Proof. solve_decision. Qed.

Global Instance into_val_interface `{ffi_syntax} : IntoVal interface.t :=
  {|
    to_val_def (i: interface.t) :=
      InjLV (#"NO TYPE IDS YET", i.(interface.v), (struct.fields_val i.(interface.mset)))
  |}.

End instances.
Global Notation "()" := tt : val_scope.

Global Opaque to_val.

Section val_types.

  (* This type is never supposed to be used in real code; if you're ever forced
     to deal with it in a proof, then something in Goose must have gone
     wrong. *)
  Definition badT_def := ptrT.
  Program Definition badT := unseal (_:seal (@badT_def)). Obligation 1. by eexists. Qed.
  Definition badT_unseal : badT = _ := seal_eq _.

  Definition byteT := uint8T.
  Definition intT := int64T.

  Context `{ffi_syntax}.
  Fixpoint zero_val_def (t : go_type) : val :=
    match t with
    | boolT => #false

    (* Numeric, except float and impl-specific sized objects *)
    | uint8T => #(W8 0)
    | uint16T => #null
    | uint32T => #(W32 0)
    | uint64T => #(W64 0)
    | int8T => #(W8 0)
    | int16T => #null
    | int32T => #(W32 0)
    | int64T => #(W64 0)

    | stringT => #""
    | arrayT n elem => fold_right PairV #() (replicate n (zero_val_def elem))
    | sliceT => #slice.nil
    | structT decls => fold_right PairV #() (fmap (zero_val_def ∘ snd) decls)
    | ptrT => #null
    | funcT => #func.nil
    | interfaceT => #interface.nil
    | mapT _ _ => #null
    | chanT _ => #null
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
    | arrayT n e => n * (go_type_size_def e)
    | _ => 1
    end.
  Program Definition go_type_size := unseal (_:seal (@go_type_size_def)). Obligation 1. by eexists. Qed.
  Definition go_type_size_unseal : go_type_size = _ := seal_eq _.
End val_types.

Reserved Notation "l +ₗ[ t ] z" (at level 50, left associativity, format "l  +ₗ[ t ]  z").
Notation "l +ₗ[ t ] z" := (l +ₗ go_type_size t * z) : stdpp_scope .
Notation "e1 +ₗ[ t ] e2" := (BinOp (OffsetOp (go_type_size t)) e1%E e2%E) : expr_scope .

(* Shortcircuit Boolean connectives *)
Notation "e1 && e2" :=
  (If e1%E e2%E #false) (only parsing) : expr_scope.
Notation "e1 || e2" :=
  (If e1%E #true e2%E) (only parsing) : expr_scope.
