From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import struct typing.

Module interface.
Section goose_lang.
Context `{ffi_syntax}.

Definition get (f : go_string) : val :=
  λ: "v",
    let: "v" := (match: "v" with InjL "v" => "v" | InjR <> => #() end) in
    let: (("typeid", "val"), "mset") := "v" in
    (match: (struct.assocl_lookup #f "mset") with
       InjL <> => #()
     | InjR "m" => "m"
     end) "val"
.

Local Definition make_def (mset : list (go_string*val)) : val :=
  λ: "v", InjL (#"NO TYPE IDS YET", "v", (struct.fields_val mset)).
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

(* method sets for primitive types are empty *)
Section mset.
Context `{ffi_syntax}.
Definition uint64__mset : list (go_string * val) := [].
Definition int__mset : list (go_string * val) := [].
Definition bool__mset : list (go_string * val) := [].
Definition string__mset : list (go_string * val) := [].
Definition slice__mset : list (go_string * val) := [].
Definition slice__mset_ptr : list (go_string * val) := [].
End mset.
