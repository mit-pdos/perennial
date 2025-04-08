From Perennial.goose_lang Require Import lang notation.
From New.golang.defn Require Export typing.
From New.golang.defn Require Import list.
From Perennial Require Import base.

Set Default Proof Using "Type".

Section defn.
Context `{ffi_syntax}.

Fixpoint type_to_val (t: go_type): val :=
  match t with
  | boolT => InjLV (# (W64 0))
  | uint8T => InjLV (# (W64 1))
  | uint16T => InjLV (# (W64 2))
  | uint32T => InjLV (# (W64 3))
  | uint64T => InjLV (# (W64 4))
  | stringT => InjLV (# (W64 5))
  | arrayT n elem => InjRV (InjLV (LitV n, type_to_val elem))
  | sliceT => InjLV (# (W64 6))
  | interfaceT => InjLV (# (W64 7))
  | structT decls =>
      let decls' := (fix go (decls: list (go_string * go_type)) :=
                       match decls with
                       | [] => InjLV #()
                       | (d, t) :: decls => InjRV ((#d, type_to_val t), go decls)
                       end
                    ) decls in
      InjRV (InjRV (InjLV decls'))
  | ptrT => InjLV (# (W64 8))
  | funcT => InjLV (# (W64 9))
  end.

#[global]
Instance go_type_into_val : IntoVal go_type :=
  { to_val_def := type_to_val; }.

End defn.
