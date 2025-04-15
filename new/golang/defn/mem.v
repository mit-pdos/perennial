From Perennial.goose_lang Require Import lang notation.
From New.golang.defn Require Import assume list dynamic_typing.
From New.golang.defn Require Export typing.
From Perennial Require Import base.

Section defn.
Context `{ffi_syntax}.

(* l +ₗ[t] i, but with a dynamic type. This is not provided as a notation. *)
Definition array_loc_add_def : val :=
  λ: "t" "l" "i",
    let: "sz" := type.go_type_size "t" in
    assume_mul_no_overflow "sz" "i";;
    "l" +ₗ ("sz" * "i").
Program Definition array_loc_add := sealed @array_loc_add_def.
Definition array_loc_add_unseal : array_loc_add = _ := seal_eq _.

Definition alloc_def : val := λ: "v", ref (Var "v").
Program Definition alloc := sealed @alloc_def.
Definition alloc_unseal : alloc = _ := seal_eq _.

Definition load_ty_def: val :=
  rec: "go" "t" "l" :=
    type.Match "t"
      (λ: <>, !"l")
      (λ: "n" "t",
        let: "size" := type.go_type_size "t" in
        (rec: "go_arr" "n" "l" :=
           let: "l_new" := "l" +ₗ "size" in
           if: "n" = #(W64 0) then #()
           else ("go" "t" "l", "go_arr" ("n" - #(W64 1)) "l_new")
        ) "n" "l")
      (λ: "decls",
        (rec: "go_struct" "decls" "l" :=
           list.Match "decls"
                      (λ: <>, #())
                      (λ: "hd" "decls", let: ("f", "t") := "hd" in
                          ("go" "t" "l", "go_struct" "decls" ("l" +ₗ type.go_type_size "t")))
        ) "decls" "l")
      .
Program Definition load_ty := sealed @load_ty_def.
Definition load_ty_unseal : @load_ty = _ := seal_eq _.

Definition store_ty_def: val :=
  rec: "go" "t" "l" "v" :=
    type.Match "t"
      (λ: <>, "l" <- "v")
      (λ: "n" "t",
        let: "size" := type.go_type_size "t" in
        (rec: "go_arr" "n" "l" "v" :=
           let: "l_new" := "l" +ₗ "size" in
           if: "n" = #(W64 0) then #()
           else "go" "t" "l" (Fst "v");; "go_arr" ("n" - #(W64 1)) "l_new" (Snd "v")
        ) "n" "l" "v")
      (λ: "decls",
        (rec: "go_struct" "decls" "l" "v" :=
           list.Match "decls"
                      (λ: <>, #())
                      (λ: "hd" "decls", let: ("f", "t") := "hd" in
                          "go" "t" "l" (Fst "v");;
                          "go_struct" "decls" ("l" +ₗ type.go_type_size "t") (Snd "v"))
        ) "decls" "l" "v")
      .
Program Definition store_ty := sealed @store_ty_def.
Definition store_ty_unseal : @store_ty = _ := seal_eq _.

End defn.

Reserved Notation "![ t ] e" (at level 9, right associativity, format "![ t ]  e").
Notation "![ t ] e" := (load_ty t%E e%E) : expr_scope.
Reserved Notation "e1 <-[ t ] e2" (at level 80, format "e1  <-[ t ]  e2").
Notation "e1 <-[ t ] e2" := (store_ty t%E e1%E e2%E) : expr_scope.
