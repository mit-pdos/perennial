From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import struct typing globals.

Module interface.
Section goose_lang.
Context `{ffi_syntax}.

Definition get_def : val :=
  λ: "method_name" "v",
    let: ("pkg_type_name", "val") := globals.unwrap "v" in
    let: ("pkg_name", "type_name") := globals.unwrap "pkg_type_name" in
    method_call "pkg_name" "type_name" "method_name" "val"
.
Program Definition get := unseal (_:seal (@get_def)). Obligation 1. by eexists. Qed.
Definition get_unseal : get = _ := seal_eq _.

Local Definition make_def : val :=
  λ: "pkg_name" "type_name" "v", InjR (InjR ("pkg_name", "type_name"), "v").
Program Definition make := unseal (_:seal (@make_def)). Obligation 1. by eexists. Qed.
Definition make_unseal : make = _ := seal_eq _.

Definition equals : val :=
  λ: "v1 v2",
    let: "v1" := (match: "v1" with InjL "v1" => "v1" | InjR <> => #() end) in
    let: "v2" := (match: "v2" with InjL "v2" => "v2" | InjR <> => #() end) in
    (Snd (Fst "v1")) = (Snd (Fst "v2"))
.

End goose_lang.
End interface.
