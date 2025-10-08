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
Definition uint64 : go.type := go.Named "uint64"%go [].
Definition uint32 : go.type := go.Named "uint32"%go [].
Definition uint16 : go.type := go.Named "uint16"%go [].
Definition uint8 : go.type := go.Named "uint8"%go [].
Definition int64 : go.type := go.Named "int64"%go [].
Definition int32 : go.type := go.Named "int32"%go [].
Definition int16 : go.type := go.Named "int16"%go [].
Definition int8 : go.type := go.Named "int8"%go [].

Definition primitives : gmap go_string mem.type :=
  {["uint64"%go := mem.w64T;
    "uint32"%go := mem.w32T;
    "uint16"%go := mem.w16T;
    "uint8"%go := mem.w8T;
    "int64"%go := mem.w64T;
    "int32"%go := mem.w32T;
    "int16"%go := mem.w16T;
    "int8"%go := mem.w8T
  ]}.

Module go.
Section defs.
Context `{!NamedUnderlyingTypes}.

Local Definition to_mem_type_aux (recur : go.type → mem.type) (t : go.type) : mem.type :=
  match t with
  | go.Named n [] =>
      match primitives !! n with
      | Some mt => mt
      | None => recur (named_to_underlying n [])
      end
  | go.PointerType _ => mem.ptrT
  | go.StructType field_decls =>
      mem.structT
        ((λ f, match f with
               | go.FieldDecl fn ty => (fn, recur ty)
               | go.EmbeddedField fn ty => (fn, recur ty)
               end) <$> field_decls)
  | _ => mem.invalidT
  end.

Local Definition to_mem_type_fuel (fuel : positive) : go.type → mem.type :=
  Pos.peano_rect
    (const (go.type → mem.type)) (λ _, mem.invalidT)
    (λ _ recur, to_mem_type_aux recur)
    fuel.

Definition to_mem_type := to_mem_type_fuel 1024.

Lemma to_mem_type_fuel_step fuel t :
  (fuel ≠ 1)%positive →
  to_mem_type_fuel fuel t =
  (to_mem_type_aux (to_mem_type_fuel (fuel-1)) t).
Proof.
  intros Hf.
  unfold to_mem_type_fuel.
  replace (fuel) with (Pos.succ (fuel-1)) by lia.
  rewrite Pos.peano_rect_succ.
  f_equal. f_equal. lia.
Qed.

Context `{ffi_syntax}.

Definition alloc_def (V : Type) `{!IntoVal V} : val := (λ: <>, ref #(zero_val V)).
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
