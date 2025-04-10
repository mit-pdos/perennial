From Perennial.goose_lang Require Import lang notation.
From New.golang.defn Require Import assume list dynamic_typing.
From New.golang.defn Require Export typing.
From Perennial Require Import base.

(* note: same names as mem.v, use only one of the two *)
Section defn.
Context `{ffi_syntax}.

(* note this takes a type to make it syntactically part of the code, but it is
not needed at runtime (same as the mem.v version, except that we take the
type as a GooseLang argument rather than a Gallina argument) *)
Definition ref_ty_def : val := λ: "t" "v", ref (Var "v").
Program Definition ref_ty := sealed @ref_ty_def.
Definition ref_ty_unseal : ref_ty = _ := seal_eq _.

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
