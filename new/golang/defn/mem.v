From New.golang.defn Require Export typing.
From Perennial Require Import base.

(** * Memory load, store, and allocation with type annotations. *)
Section go_lang.
  Context `{ffi_syntax}.

  Definition ref_ty_def (t : go_type) : val := λ: "v", ref (Var "v").
  Program Definition ref_ty := sealed @ref_ty_def.
  Definition ref_ty_unseal : ref_ty = _ := seal_eq _.

  Fixpoint load_ty_def (t : go_type) : val :=
    match t with
    | structT d =>
        (fix load_ty_struct d : val :=
          match d with
          | [] => (λ: <>, #())%V
          | (_,t) :: d => (λ: "l", (load_ty_def t "l", load_ty_struct d ("l" +ₗ[t] #(W64 1))))%V
          end) d
    | arrayT n t =>
        (fix load_ty_array n : val :=
          match n with
          | O => (λ: <>, #())%V
          | S n => (λ: "l", (load_ty_def t "l", load_ty_array n ("l" +ₗ[t] #(W64 1))))%V
          end) n
    | _ => (λ: "l", !(Var "l"))%V
    end.
  Program Definition load_ty := sealed @load_ty_def.
  Definition load_ty_unseal : load_ty = _ := seal_eq _.

  Fixpoint store_ty_def (t : go_type): val :=
    match t with
    | structT d =>
        (fix store_ty_struct d : val :=
          match d with
          | [] => (λ: <> <>, #())%V
          | (f,t) :: d => (λ: "p" "v",
                                  store_ty_def t "p" (Fst "v");;
                                  store_ty_struct d (BinOp (OffsetOp (go_type_size t)) "p" #(W64 1))
                                    (Snd "v"))%V
          end) d
    | arrayT n t =>
        (fix store_ty_array n : val :=
          match n with
          | O => (λ: <> <>, #())%V
          | S n => (λ: "p" "v",
                            store_ty_def t "p" (Fst "v");;
                            store_ty_array n (BinOp (OffsetOp (go_type_size t)) "p" #(W64 1)) (Snd "v"))%V
          end) n
    | _ => (λ: "p" "v", "p" <- "v")%V
    end.
  Program Definition store_ty := sealed @store_ty_def.
  Definition store_ty_unseal : store_ty = _ := seal_eq _.

End go_lang.

Reserved Notation "![ t ] e" (at level 9, right associativity, format "![ t ]  e").
Notation "![ t ] e" := (load_ty t e%E) : expr_scope.
Reserved Notation "e1 <-[ t ] e2" (at level 80, format "e1  <-[ t ]  e2").
Notation "e1 <-[ t ] e2" := (store_ty t e1%E e2%E) : expr_scope.
