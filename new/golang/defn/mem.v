From New.golang.defn Require Export typing.
From Perennial Require Import base.

(** * Memory load, store, and allocation with type annotations. *)
Module mem.
Section go_lang.
  Context `{ffi_syntax}.

  Definition alloc_def (t : go_type) : val := λ: <>, ref (zero_val t).
  Program Definition alloc := sealed @alloc_def.
  Definition alloc_unseal : alloc = _ := seal_eq _.

  Fixpoint load_def (t : go_type) : val :=
    match t with
    | structT d =>
        (fix load_struct d : val :=
          match d with
          | [] => (λ: <>, #())%V
          | (_,t) :: d => (λ: "l", (load_def t "l", load_struct d ("l" +ₗ[t] #(W64 1))))%V
          end) d
    | arrayT n t =>
        (fix load_array n : val :=
          match n with
          | O => (λ: <>, #())%V
          | S n => (λ: "l", (load_def t "l", load_array n ("l" +ₗ[t] #(W64 1))))%V
          end) n
    | _ => (λ: "l", !(Var "l"))%V
    end.
  Program Definition load := sealed @load_def.
  Definition load_unseal : load = _ := seal_eq _.

  Fixpoint store_def (t : go_type): val :=
    match t with
    | structT d =>
        (fix store_struct d : val :=
          match d with
          | [] => (λ: <> <>, #())%V
          | (f,t) :: d => (λ: "p" "v",
                                  store_def t "p" (Fst "v");;
                                  store_struct d (BinOp (OffsetOp (go_type_size t)) "p" #(W64 1))
                                    (Snd "v"))%V
          end) d
    | arrayT n t =>
        (fix store_array n : val :=
          match n with
          | O => (λ: <> <>, #())%V
          | S n => (λ: "p" "v",
                            store_def t "p" (Fst "v");;
                            store_array n (BinOp (OffsetOp (go_type_size t)) "p" #(W64 1)) (Snd "v"))%V
          end) n
    | _ => (λ: "p" "v", "p" <- "v")%V
    end.
  Program Definition store := sealed @store_def.
  Definition store_unseal : store = _ := seal_eq _.

End go_lang.
End mem.

Reserved Notation "![ t ] e" (at level 9, right associativity, format "![ t ]  e").
Notation "![ t ] e" := (mem.load t e%E) : expr_scope.
Reserved Notation "e1 <-[ t ] e2" (at level 80, format "e1  <-[ t ]  e2").
Notation "e1 <-[ t ] e2" := (mem.store t e1%E e2%E) : expr_scope.
