From New.golang.defn Require Import list dynamic_typing.
From Perennial Require Import base.

(* cannot be export *)
#[global] Open Scope Z_scope.

(* FIXME: these notations don't work properly. *)
Declare Scope struct_scope.
Notation "f :: t" := (@pair go_string go_type f%go t) : struct_scope.
Notation "f ::= v" := (PairV #(f%go) v%V) (at level 60) : val_scope.
Notation "f ::= v" := (Pair #(f%go) v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.
Global Arguments structT _%_list%_struct.

Module struct.
Section goose_lang.
Infix "=?" := (ByteString.eqb).

Context `{ffi_syntax}.

Definition field_offset : val :=
  λ: "t" "f",
    let: "missing" := #(W64 (2^64-1)) in
    type.Match "t"
               (λ: <>, ("missing", #badT))
               (λ: "n" "et", ("missing", #badT)) (* arrayT *)
               (λ: "decls",
               (rec: "field_offset_struct" "fs" :=
                   list.Match "fs"
                              (λ: <>, ("missing", #badT))
                              (λ: "hd" "fs", let: ("f'", "t") := "hd" in
                                  if: "f'" = "f" then (#(W64 0), "t")
                                  else
                                    let: ("off", "t'") := "field_offset_struct" "fs" in
                                    (type.go_type_size "t" + "off", "t'"))
               ) "decls")
.

Definition field_ref : val :=
  λ: "t" "f" "p", BinOp (OffsetOp 1%Z) (Var "p") (Fst (field_offset "t" "f")).

Definition field_get : val :=
  λ: "t" "f" "v",
    type.Match "t"
               (λ: <>, #())
               (λ: "n" "et", #()) (* arrayT *)
               (λ: "decls",
               (rec: "field_get_struct" "fs" :=
                   list.Match "fs"
                              (λ: <>, #())
                              (λ: "hd" "fs", let: ("f'", <>) := "hd" in
                                  if: "f'" = "f"
                                  then (Fst "v")
                                  else "field_get_struct" "fs" (Snd "v"))
               ) "decls").

Definition make_def : val :=
  λ: "t" "fvs",
    type.Match "t"
               (λ: <>, LitV (LitPoison))
               (λ: "n" "et", LitV (LitPoison)) (* arrayT *)
               (λ: "decls",
               (rec: "make_struct" "fs" :=
                   list.Match "fs"
                              (λ: <>, #())
                              (λ: "hd" "fs", let: ("f", "ft") := "hd" in
                                  ((match: (alist_lookup "f" "fvs") with
                                    InjL <> => type.zero_val "ft"
                                  | InjR "x" => "x" end),
                                    "make_struct" "fs"))
               ) "decls").
Program Definition make := sealed @make_def.
Definition make_unseal : make = _ := seal_eq _.

End goose_lang.
End struct.

Notation "[{ }]" := (alist_val []) (only parsing) : expr_scope.
Notation "[{ x }]" := (list.Cons x [{ }]%E) : expr_scope.
Notation "[{ x ; y ; .. ; z }]" := (list.Cons x (list.Cons y .. (list.Cons z [{ }]%E) ..)) : expr_scope.
