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
                       | [] => list.Nil
                       | (d, t) :: decls => list.ConsV (#d, type_to_val t) (go decls)
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

Definition arrayT: val := λ: "n" "elemT", InjR (InjL ("n", "elemT")).
Definition structT: val := λ: "decls", InjR (InjR (InjL "decls")).
Definition mapT: val := λ: "keyT" "elemT", #ptrT.
Definition chanT: val := λ: "elemT", #ptrT.

Definition Match_def : val :=
  λ: "t" "baseCase" "arrayCase" "structCase",
    match: "t" with
      InjL "x" => "baseCase" (InjL "x")
    | InjR "x" => match: "x" with
        InjL "arr" => let: ("n", "t") := "arr" in
                    "arrayCase" "n" "t"
      | InjR "x" => match: "x" with
          InjL "decls" => "structCase" "decls"
        | InjR <> => Panic "dynamic_typing.Match: unreachable"
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

Definition zero_val_def: val :=
  rec: "zero_val" "t" :=
    Match "t"
          (λ: "x",
            let: "n" := (match: "x" with InjL "n" => "n" | InjR <> => Panic "zero_val: unreachable" end) in
            if: "n" = #(W64 0) then
              #false
            else if: "n" = #(W64 1) then
                 #"000"%go_byte
            else if: "n" = #(W64 2) then
                #null (* uint16 *)
            else if: "n" = #(W64 3) then
                 #(W32 0)
            else if: "n" = #(W64 4) then
                 #(W64 0)
            else if: "n" = #(W64 5) then
                   #""%go
            else if: "n" = #(W64 6) then
                   #slice.nil
            else if: "n" = #(W64 7) then
                   #interface.nil
            else if: "n" = #(W64 9) then
                   #func.nil
            else #null (* catch-all and pointer (n = 8) case *)
          )
          (λ: "n" "elem",
            (rec: "go" "n" :=
               if: "n" = #(W64 0) then #()
               else ("zero_val" "elem", "go" ("n" - #(W64 1)))
            ) "n")
          (λ: "decls",
            (rec: "go" "decls" :=
               list.Match "decls"
                          (λ: <>, #())
                          (λ: "hd" "decls", let: ("f", "ft") := "hd" in
                              ("zero_val" "ft", "go" "decls"))
            ) "decls"
          ).
Program Definition zero_val := sealed @zero_val_def.
Definition zero_val_unseal : @zero_val = _ := seal_eq _.


End defn.
End type.
