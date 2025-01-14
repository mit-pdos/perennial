From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import struct typing globals.

Module interface.
Section goose_lang.
Context `{ffi_syntax}.

Definition get (f : go_string) : val :=
  λ: "v",
    let: "v" := (match: "v" with SOME "v" => "v" | NONE => #() #() end) in
    let: ("pkg_type_name", "val") := "v" in
    (match: GlobalGet (#"method:"%go + "encoded_type_name" + #" "%go + #f) with
       InjL <> => #() #()
     | InjR "m" => "m"
     end) "val".

Local Definition make_def (pkg_type_name : go_string * go_string): val :=
  λ: "v", InjR (InjRV (#pkg_type_name.1, #pkg_type_name.2), "v").
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
