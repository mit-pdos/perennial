From New.golang.defn Require Export typing intoval.
From Perennial Require Import base.

Module mem.
Inductive type :=
(* Boolean *)
| boolT

(* Numeric, except float and impl-specific sized objects *)
| w8T
| w16T
| w32T
| w64T
| stringT
| arrayT (n : nat) (elem : type)
| sliceT
| interfaceT
| structT (decls : list (go_string * type))
| ptrT
| funcT
| invalidT.

Section val_types.
  Context `{ffi_syntax}.
  Fixpoint zero_val (t : type) : val :=
    match t with
    | boolT => #false

    (* Numeric, except float and impl-specific sized objects *)
    | w8T => #(W8 0)
    | w16T => #(W16 0)
    | w32T => #(W32 0)
    | w64T => #(W64 0)

    | stringT => #""%V
    | arrayT n elem => fold_right PairV #() (replicate n (zero_val elem))
    | sliceT => #slice.nil
    | structT decls => fold_right PairV #() (fmap (zero_val ∘ snd) decls)
    | ptrT => #null
    | funcT => #func.nil
    | interfaceT => #interface.nil
    | invalidT => LitV LitPoison
    end.

  Fixpoint type_size (t : type) : nat :=
    match t with
    | structT d =>
        (fix type_size_struct d : nat :=
           match d with
           | [] => O
           | (_,t) :: d => (type_size t + type_size_struct d)%nat
           end
        ) d
    | arrayT n e => n * (type_size e)
    | _ => 1
    end.
End val_types.

Reserved Notation "l +ₗ[ t ] z" (at level 50, left associativity, format "l  +ₗ[ t ]  z").
Global Notation "l +ₗ[ t ] z" := (l +ₗ type_size t * z) : stdpp_scope .
Global Notation "e1 +ₗ[ t ] e2" := (BinOp (OffsetOp (type_size t)) e1%E e2%E) : expr_scope .

(** * Memory load, store, and allocation with type annotations. *)
Section go_lang.
  Context `{ffi_syntax}.
  Context `{!NamedUnderlyingTypes}.

  Definition alloc (t : type) : val := λ: <>, ref (zero_val t).

  Fixpoint load (t : type) : val :=
    match t with
    | structT d =>
        (fix load_struct d : val :=
          match d with
          | [] => (λ: <>, #())%V
          | (_,t) :: d => (λ: "l", (load t "l", load_struct d ("l" +ₗ[t] #(W64 1))))%V
          end) d
    | arrayT n t =>
        (fix load_array n : val :=
          match n with
          | O => (λ: <>, #())%V
          | S n => (λ: "l", (load t "l", load_array n ("l" +ₗ[t] #(W64 1))))%V
          end) n
    | invalidT => (λ: "l", Panic "invalid type")%V
    | _ => (λ: "l", !(Var "l"))%V
    end.

  Fixpoint store (t : type): val :=
    match t with
    | structT d =>
        (fix store_struct d : val :=
          match d with
          | [] => (λ: <> <>, #())%V
          | (f,t) :: d => (λ: "p" "v",
                                  store t "p" (Fst "v");;
                                  store_struct d (BinOp (OffsetOp (type_size t)) "p" #(W64 1))
                                    (Snd "v"))%V
          end) d
    | arrayT n t =>
        (fix store_array n : val :=
          match n with
          | O => (λ: <> <>, #())%V
          | S n => (λ: "p" "v",
                            store t "p" (Fst "v");;
                            store_array n (BinOp (OffsetOp (type_size t)) "p" #(W64 1)) (Snd "v"))%V
          end) n
    | invalidT => (λ: "l", Panic "invalid type")%V
    | _ => (λ: "p" "v", "p" <- "v")%V
    end.
End go_lang.
End mem.

(* built-in types *)
Definition uint64 : go_string := "uint64".
Definition uint16 : go_string := "uint16".
Definition uint8 : go_string := "uint8".
Definition int64 : go_string := "int64".
Definition int32 : go_string := "int32".
Definition int16 : go_string := "int16".
Definition int8 : go_string := "int8".

Module go.
Section defs.
Context `{!NamedUnderlyingTypes}.

Local Definition to_mem_type (t : go.type) : mem.type :=
  match t with
  | go.Named n (go.TypeArgs []) =>
      if decide (n = uint64) then mem.w64T
      else mem.invalidT
  | _ => mem.invalidT
  end.

Context `{ffi_syntax}.

Definition alloc_def (t : go.type) : val := mem.alloc (to_mem_type t).
Program Definition alloc := sealed @alloc_def.
Definition alloc_unseal : alloc = _ := seal_eq _.

Definition load_def (t : go.type) : val := mem.load (to_mem_type t).
Program Definition load := sealed @load_def.
Definition load_unseal : load = _ := seal_eq _.

Definition store_def (t : go.type) : val := mem.store (to_mem_type t).
Program Definition store := sealed @store_def.
Definition store_unseal : store = _ := seal_eq _.

End defs.
End go.
