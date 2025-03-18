From New Require Import notation.
From New.golang.defn Require Import typing.
From Perennial Require Import base.

Module list.
Section defn.
  Context `{ffi_syntax}.

  Definition Nil_def : val := InjLV #().
  Program Definition Nil := unseal (_:seal (@Nil_def)).
  Definition Nil_unseal : Nil = _ := seal_eq _.

  Definition Cons_def : val := λ: "h" "tl", InjR ("h", "tl").
  Program Definition Cons := unseal (_:seal (@Cons_def)).
  Definition Cons_unseal : Cons = _ := seal_eq _.

  Definition Match_def : val :=
    λ: "l" "nilCase" "consCase",
      Match "l"
        <> ("nilCase" #())
        "x" (let: ("hd", "tl") := "x" in "consCase" "hd" "tl").
  Program Definition Match := unseal (_:seal (@Match_def)).
  Definition Match_unseal : Match = _ := seal_eq _.

  Definition Length : val :=
    rec: "length" "l" := Match "l" (λ: <>, #(W64 0))
                           (λ: "hd" "tl",
                              let: "tl_length" := ("length" "tl") in
                              let: "new_length" := #(W64 1) + "tl_length" in
                              if: "new_length" > "tl_length" then
                                "new_length"
                              else (rec: "infloop" <> := Var "infloop" #()) #()
                           ).
End defn.
End list.

Section defn.
Context `{ffi_syntax}.
Definition alist_lookup : val :=
  rec: "alist_lookup" "f" "fvs" :=
    list.Match "fvs"
              (λ: <>, InjLV #())
              (λ: "fv" "fvs",
                 let: ("f'", "v") := "fv" in
                 if: "f" = "f'" then SOME "v" else "alist_lookup" "f" "fvs").

Fixpoint alist_val_def (m : list (go_string * val)) : val :=
  match m with
  | [] => InjLV #()
  | (f, v) :: tl => InjRV ((#f, v), alist_val_def tl)
  end.
Program Definition alist_val := unseal (_:seal (@alist_val_def)).
Definition alist_val_unseal : alist_val = _ := seal_eq _.

End defn.

Notation "[ ]" := (list.Nil) (only parsing) : expr_scope.
Notation "[ x ]" := (list.Cons x []%E) : expr_scope.
Notation "[ x ; y ; .. ; z ]" := (list.Cons x (list.Cons y .. (list.Cons z []%E) ..)) : expr_scope.
