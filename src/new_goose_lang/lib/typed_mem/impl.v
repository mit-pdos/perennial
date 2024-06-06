From Perennial.goose_lang Require Import notation.
From Perennial.new_goose_lang Require Import typing.

Reserved Notation "![ t ] e"
         (at level 9, right associativity, format "![ t ]  e").
Reserved Notation "e1 <-[ t ] e2"
         (at level 80, format "e1  <-[ t ]  e2").

Section go_lang.
  Context `{ffi_syntax}.

  (** allocation with a type annotation *)
  Definition ref_to (t:go_type): val := λ: "v", ref (Var "v").
  Definition ref_zero (t:go_type): val := λ: <>, ref (zero_val t).

  Inductive go_abstract_type :=
  | cellT
  | unitT
  | prodT (t1 t2 : go_abstract_type)
  .
  Fixpoint go_abstract_type_size (t : go_abstract_type) : nat :=
    match t with
    | prodT t1 t2 => go_abstract_type_size t1 + go_abstract_type_size t2
    | cellT => 1
    | unitT => 0
    end.

  Fixpoint go_type_interp (t : go_type) : go_abstract_type :=
    match t with
    | sliceT _ => prodT cellT $ prodT cellT $ prodT cellT unitT
    | structT decls => fold_right prodT unitT (fmap (go_type_interp ∘ snd) decls)
    | interfaceT => prodT cellT $ prodT cellT$ prodT cellT unitT (* type id, val, methods *)
    | _ => cellT
    end.

  Definition go_type_size (t : go_type) : nat := go_abstract_type_size $ go_type_interp t.

  (* TODO: seal *)
  Definition load_ty (t : go_type) : val :=
    (fix load_ty_aux t : val :=
      match t with
      | prodT t1 t2 => (λ: "l", (load_ty_aux t1 (Var "l"),
                                  load_ty_aux t2 (Var "l" +ₗ #(go_abstract_type_size t1))))%V
      | cellT => (λ: "l", !(Var "l"))%V
      | unitT => (λ: <>, #())%V
      end) (go_type_interp t).

  Definition store_ty t: val :=
    (fix store_ty_aux t : val :=
       match t with
       | prodT t1 t2 => (λ: "pv",
                         let: "p" := Fst (Var "pv") in
                         let: "v" := Snd (Var "pv") in
                         store_ty_aux t1 (Var "p", Fst (Var "v"));;
                         store_ty_aux t2 (Var "p" +ₗ #(go_abstract_type_size t1), Snd (Var "v")))%V
       | cellT => (λ: "pv", Fst (Var "pv") <- Snd (Var "pv"))%V
       | unitT => (λ: <>, #())%V
       end) (go_type_interp t).

  Definition ref_ty (t : go_type) : val := λ: "v", ref (Var "v").
End go_lang.

Notation "![ t ] e" := (load_ty t e%E) : expr_scope.
(* NOTE: in code we want to supply arbitrary expressions, so we have the usual
   notation, but the specs should be in terms of value pairs, so we have a
   similar notation in the value-scope (even though this is an expression and
   not a value)

   See the HeapLang documentation in Iris for par, which has a similar
   trick. *)
Notation "e1 <-[ t ] e2" := (store_ty t (Pair e1%E e2%E)) : expr_scope.
Notation "v1 <-[ t ] v2" := (store_ty t (PairV v1%V v2%V)) : val_scope.

Reserved Notation "l +ₗ[ t ] z" (at level 50, left associativity, format "l  +ₗ[ t ]  z").
Notation "l +ₗ[ t ] z" := (l +ₗ go_abstract_type_size (go_type_interp t) * z) : stdpp_scope .
Notation "e1 +ₗ[ t ] e2" := (BinOp (OffsetOp (go_abstract_type_size $ go_type_interp t)) e1%E e2%E) : expr_scope .
