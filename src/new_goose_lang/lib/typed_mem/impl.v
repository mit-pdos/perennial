From Perennial.goose_lang Require Import notation.
From Perennial.new_goose_lang Require Import typing.

Reserved Notation "![ t ] e"
         (at level 9, right associativity, format "![ t ]  e").
Reserved Notation "e1 <-[ t ] e2"
         (at level 80, format "e1  <-[ t ]  e2").

Fixpoint go_type_size (t : go_type) : nat :=
  match t with
  | structT d =>
      (fix go_type_size_struct d : nat :=
        match d with
        | [] => O
        | (_,t) :: d => (go_type_size t + go_type_size_struct d)%nat
        end
      ) d
  | sliceT e => 3
  | interfaceT => 3
  | _ => 1
  end.


Reserved Notation "l +ₗ[ t ] z" (at level 50, left associativity, format "l  +ₗ[ t ]  z").
Notation "l +ₗ[ t ] z" := (l +ₗ go_type_size t * z) : stdpp_scope .
Notation "e1 +ₗ[ t ] e2" := (BinOp (OffsetOp (go_type_size t)) e1%E e2%E) : expr_scope .

Section go_lang.
  Context `{ffi_syntax}.
  Local Coercion Var' (s:string): expr := Var s.

  (** allocation with a type annotation *)
  Definition ref_to (t:go_type): val := λ: "v", ref (Var "v").

  (* TODO: seal *)
  Definition load_ty (t : go_type) : val :=
    match t with
    | structT d =>
        (fix store_struct d : val :=
          match d with
          | [] => (λ: <>, #())%V
          | (f,t) :: d => (λ: "pv", let: "p" := Fst "pv" in
                                  let: "v" := Snd "pv" in
                                  store_ty_aux t ("p", Fst "v");;
                                  store_struct d (BinOp (OffsetOp (go_type_size t))
                                                        "p" #1, Snd "v"))%V
          end) d
    | sliceT e =>
        (λ: "pv", let: "p" := Fst "pv" in
                  let: "v" := Snd "pv" in
                  let: (("a", "b"), "c") := "v" in
                  "p" +ₗ #0 <- "a" ;;
                  "p" +ₗ #1 <- "b" ;;
                  "p" +ₗ #2 <- "c"
        )%V

    | interfaceT =>
        (λ: "pv", let: "p" := Fst "pv" in
                  let: "v" := Snd "pv" in
                  let: (("a", "b"), "c") := "v" in
                  "p" +ₗ #0 <- "a" ;;
                  "p" +ₗ #1 <- "b" ;;
                  "p" +ₗ #2 <- "c"
        )%V

    | cellT => (λ: "l", !(Var "l"))%V
    end.

    match t with
    | prodT t1 t2 => (λ: "l", (load_ty_aux t1 (Var "l"),
                               load_ty_aux t2 (BinOp (OffsetOp (go_abstract_type_size t1))
                                                     (Var "l") #1)))%V
    | cellT => (λ: "l", !(Var "l"))%V
    | unitT => (λ: <>, #())%V
    end) (go_type_interp t).

  Fixpoint store_ty (t : go_type): val :=
    match t with
    | structT d =>
        (fix store_struct d : val :=
          match d with
          | [] => (λ: <>, #())%V
          | (f,t) :: d => (λ: "pv", let: "p" := Fst "pv" in
                                  let: "v" := Snd "pv" in
                                  store_ty_aux t ("p", Fst "v");;
                                  store_struct d (BinOp (OffsetOp (go_type_size t))
                                                        "p" #1, Snd "v"))%V
          end) d
    | sliceT e =>
        (λ: "pv", let: "p" := Fst "pv" in
                  let: "v" := Snd "pv" in
                  let: (("a", "b"), "c") := "v" in
                  "p" +ₗ #0 <- "a" ;;
                  "p" +ₗ #1 <- "b" ;;
                  "p" +ₗ #2 <- "c"
        )%V

    | interfaceT =>
        (λ: "pv", let: "p" := Fst "pv" in
                  let: "v" := Snd "pv" in
                  let: (("a", "b"), "c") := "v" in
                  "p" +ₗ #0 <- "a" ;;
                  "p" +ₗ #1 <- "b" ;;
                  "p" +ₗ #2 <- "c"
        )%V

    | _ => (λ: "pv", Fst "pv" <- Snd "pv")%V
    end.

  Definition ref_ty (t : go_type) : val := λ: "v", ref (Var "v").
End go_lang.

(* otation "![ t ] e" := (load_ty t e%E) : expr_scope. *)
(* NOTE: in code we want to supply arbitrary expressions, so we have the usual
   notation, but the specs should be in terms of value pairs, so we have a
   similar notation in the value-scope (even though this is an expression and
   not a value)

   See the HeapLang documentation in Iris for par, which has a similar
   trick. *)
(* FIXME: these notations are a little messed up; they get unfolded where they shouldn't, etc. *)
Notation "e1 <-[ t ] e2" := (store_ty t (Pair e1%E e2%E)) : expr_scope.
Notation "v1 <-[ t ] v2" := (store_ty t (PairV v1%V v2%V)) : val_scope.
