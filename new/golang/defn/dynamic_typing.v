From Perennial.goose_lang Require Import lang notation.
From New.golang.defn Require Import assume list.
From New.golang.defn Require Export typing.
From Perennial Require Import base.

Module type.
Section defn.
Context `{ffi_syntax}.

(** Encode [go_type] into [val] for use within GooseLang. The encoding is injective.

The output of this roughly has type [Ty = uint64 + (uint64 * Ty + (list (string
* Ty) + void))]; keep in mind that this is type in some type system we haven't
formalized, unrelated to `go_type`, and in fact we can't even represent
recursive types in `go_type`. The left branch encodes all of the "base types"
using a unique index. The right branch is used for arrays (encoded as `uint64 *
t` for the length and element type) and structs (encoded as a list of field
names and field types). There's an unused position where the "void" is in case
we want to change something.

The list type used here is the same as the golang/defn/list library, [list a =
unit + (a * list a)].

*)
Notation ArrayT n T := (InjRV (InjLV (LitV n, T))) (only parsing).
Notation StructT decls := (InjRV (InjRV (InjLV decls))) (only parsing).
Fixpoint type_to_val (t: go_type): val :=
  match t with
  | boolT => InjLV (# (W64 0))
  | uint8T => InjLV (# (W64 1))
  | uint16T => InjLV (# (W64 2))
  | uint32T => InjLV (# (W64 3))
  | uint64T => InjLV (# (W64 4))
  | stringT => InjLV (# (W64 5))
  | arrayT n elem => ArrayT n (type_to_val elem)
  | sliceT => InjLV (# (W64 6))
  | interfaceT => InjLV (# (W64 7))
  | structT decls =>
      (* decls' is a list *)
      let decls' := (fix go (decls: list (go_string * go_type)) :=
                       match decls with
                       | [] => InjLV #()
                       | (d, t) :: decls => InjRV ((#d, type_to_val t), go decls)
                       end
                    ) decls in
      (* wrap this in the right constructor *)
      StructT decls'
  | ptrT => InjLV (# (W64 8))
  | funcT => InjLV (# (W64 9))
  end.

#[global]
Instance go_type_into_val : IntoVal go_type :=
  { to_val_def := type_to_val; }.

Definition Match_def : val :=
  λ: "t" "baseCase" "arrayCase" "structCase",
    match: "t" with
      InjL "x" => "baseCase" (InjL "x")
    | InjR "x" => match: "x" with
        InjL "arr" => let: ("n", "t") := "arr" in
                    "arrayCase" "n" "t"
      | InjR "x" => match: "x" with
          InjL "decls" => "structCase" "decls"
        | InjR <> => #() (* unreachable *)
         end
      end
    end.
Program Definition Match := sealed @Match_def.
Definition Match_unseal : Match = _ := seal_eq _.

(* would shadow [go_type_size] Gallina definition, intended to be used qualified
with module name *)
Definition go_type_size_def: val :=
  rec: "go_type_size" "t" :=
    Match "t"
      (λ: <>, #(W64 1))
      (λ: "n" "t", assume_mul_no_overflow "n" ("go_type_size" "t");;
                   "n" * "go_type_size" "t")
      (λ: "decls",
        (rec: "struct_size" "decls" :=
           list.Match "decls"
                      (λ: <>, #(W64 0))
                      (λ: "hd" "decls", let: ("f", "t") := "hd" in
                          sum_assume_no_overflow ("go_type_size" "t") ("struct_size" "decls"))
        ) "decls").
Program Definition go_type_size := sealed @go_type_size_def.
Definition go_type_size_unseal : @go_type_size = _ := seal_eq _.

End defn.
End type.
