From New.golang.defn Require Export typing.

(** * Memory load, store, and allocation with type annotations. *)
Section go_lang.
  Context `{ffi_syntax}.
  Local Coercion Var' (s:string): expr := Var s.

  Definition ref_ty_def (t : go_type) : val := λ: "v", ref (Var "v").
  Program Definition ref_ty := unseal (_:seal (@ref_ty_def)). Obligation 1. by eexists. Qed.
  Definition ref_ty_unseal : ref_ty = _ := seal_eq _.

  Fixpoint load_ty_def (t : go_type) : val :=
    match t with
    | structT d =>
        (fix load_ty_struct d : val :=
          match d with
          | [] => (λ: <>, #())%V
          | (_,t) :: d => (λ: "l", (load_ty_def t "l", load_ty_struct d ("l" +ₗ[t] #1)))%V
          end) d
    | sliceT e => (λ: "l", (!("l" +ₗ #0), !("l" +ₗ #1), !("l" +ₗ #2)))%V
    | interfaceT => (λ: "l", (!("l" +ₗ #0), !("l" +ₗ #1), !("l" +ₗ #2)))%V
    | _ => (λ: "l", !(Var "l"))%V
    end.
  Program Definition load_ty := unseal (_:seal (@load_ty_def)). Obligation 1. by eexists. Qed.
  Definition load_ty_unseal : load_ty = _ := seal_eq _.

  Fixpoint store_ty_def (t : go_type): val :=
    match t with
    | structT d =>
        (fix store_struct d : val :=
          match d with
          | [] => (λ: <>, #())%V
          | (f,t) :: d => (λ: "pv", let: "p" := Fst "pv" in
                                  let: "v" := Snd "pv" in
                                  store_ty_def t ("p", Fst "v");;
                                  store_struct d (BinOp (OffsetOp (go_type_size t))
                                                        "p" #1, Snd "v"))%V
          end) d
    | sliceT e => (λ: "pv", let: "p" := Fst "pv" in
                           let: "v" := Snd "pv" in
                           let: (("a", "b"), "c") := "v" in
                           "p" +ₗ #0 <- "a" ;;
                           "p" +ₗ #1 <- "b" ;;
                           "p" +ₗ #2 <- "c")%V
    | interfaceT => (λ: "pv", let: "p" := Fst "pv" in
                             let: "v" := Snd "pv" in
                             let: (("a", "b"), "c") := "v" in
                             "p" +ₗ #0 <- "a" ;;
                             "p" +ₗ #1 <- "b" ;;
                             "p" +ₗ #2 <- "c")%V
    | _ => (λ: "pv", Fst "pv" <- Snd "pv")%V
    end.
  Program Definition store_ty := unseal (_:seal (@store_ty_def)). Obligation 1. by eexists. Qed.
  Definition store_ty_unseal : store_ty = _ := seal_eq _.

End go_lang.

Reserved Notation "![ t ] e" (at level 9, right associativity, format "![ t ]  e").
Notation "![ t ] e" := (load_ty t e%E) : expr_scope.
(* NOTE: in code we want to supply arbitrary expressions, so we have the usual
   notation, but the specs should be in terms of value pairs, so we have a
   similar notation in the value-scope (even though this is an expression and
   not a value)

   See the HeapLang documentation in Iris for par, which has a similar
   trick. *)
(* FIXME: these notations are a little messed up; they get unfolded where they shouldn't, etc. *)
Reserved Notation "e1 <-[ t ] e2" (at level 80, format "e1  <-[ t ]  e2").
Notation "e1 <-[ t ] e2" := (store_ty t (Pair e1%E e2%E)) : expr_scope.
Notation "v1 <-[ t ] v2" := (store_ty t (PairV v1%V v2%V)) : val_scope.
