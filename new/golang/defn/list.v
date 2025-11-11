From New Require Import notation.
From New.golang.defn Require Export typing.
From Perennial Require Import base.

Module list.
Section defn.
  Context `{ffi_syntax}.

  Definition Nil_def : val := InjLV #().
  Program Definition Nil := sealed @Nil_def.
  Definition Nil_unseal : Nil = _ := seal_eq _.

  Definition Cons_def : val := λ: "h" "tl", InjR ("h", "tl").
  Program Definition Cons := sealed @Cons_def.
  Definition Cons_unseal : Cons = _ := seal_eq _.

  Definition Match_def : val :=
    λ: "l" "nilCase" "consCase",
      Match "l"
        <> ("nilCase" #())
        "x" (let: ("hd", "tl") := "x" in "consCase" "hd" "tl").
  Program Definition Match := sealed @Match_def.
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

  #[local] Definition random_int: val :=
    λ: "n", ArbitraryInt `rem` "n".

  Definition Get : val :=
    rec: "get" "l" "i" :=
      Match "l"
        (λ: <>, Panic "index out of bounds")
        (λ: "hd" "tl",
          if: "i" = #(W64 0) then
            "hd"
          else
            "get" "tl" ("i" - #(W64 1))).

  Definition Insert : val :=
    rec: "insert" "l" "i" "v" :=
      Match "l"
        (λ: <>, Nil #())
        (λ: "hd" "tl",
          if: "i" = #(W64 0) then
            Cons "v" "tl"
          else
            Cons "hd" ("insert" "tl" ("i" - #(W64 1)) "v")).

  #[local] Definition shuffle_helper: val :=
    rec: "shuffle_helper" "lst" "len" "remaining" :=
      if: "remaining" ≤ #(W64 0) then
        "lst"
      else
        let: "idx" := random_int "remaining" in
        let: "val" := Get "lst" "idx" in
        let: "last_idx" := "remaining" - #(W64 1) in
        let: "last_val" := Get "lst" "last_idx" in
        let: "lst2" := Insert "lst" "idx" "last_val" in
        let: "lst3" := Insert "lst2" "last_idx" "val" in
        "shuffle_helper" "lst3" "len" "last_idx".

  Definition Shuffle : val :=
    λ: "l",
      let: "len" := Length "l" in
      shuffle_helper "l" "len" "len".

End defn.

Notation ConsV hd tl := (InjRV (hd, tl)).
End list.

Section defn.
Context `{ffi_syntax}.
Definition alist_lookup : val :=
  rec: "alist_lookup" "f" "fvs" :=
    list.Match "fvs"
              (λ: <>, NONEV)
              (λ: "fv" "fvs",
                 let: ("f'", "v") := "fv" in
                 if: "f" = "f'" then SOME "v" else "alist_lookup" "f" "fvs").

Fixpoint alist_val_def (m : list (go_string * val)) : val :=
  match m with
  | [] => InjLV #()
  | (f, v) :: tl => InjRV ((#f, v), alist_val_def tl)
  end.
Program Definition alist_val := sealed @alist_val_def.
Definition alist_val_unseal : alist_val = _ := seal_eq _.

End defn.

Notation "[ ]" := (list.Nil) (only parsing) : expr_scope.
Notation "[ x ]" := (list.Cons x []%E) : expr_scope.
Notation "[ x ; y ; .. ; z ]" := (list.Cons x (list.Cons y .. (list.Cons z []%E) ..)) : expr_scope.

Notation "[ ]" := (list.Nil) (only parsing) : val_scope.
Notation "[ x ]" := (list.ConsV x []%V) : val_scope.
Notation "[ x ]" := (list.ConsV x []%V) : val_scope.
Notation "[ x ; y ; .. ; z ]" := (list.ConsV x (list.ConsV y .. (list.ConsV z []%V) ..)) : val_scope.
