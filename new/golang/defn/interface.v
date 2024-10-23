From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import struct typing.

Module interface.
Section goose_lang.
Context `{ffi_syntax}.

Definition get (f : string) : val :=
  λ: "v",
    let: "v" := (match: "v" with InjL "v" => "v" | InjR <> => #() end) in
    let: (("typeid", "val"), "mset") := "v" in
    (match: (struct.assocl_lookup #f "mset") with
       InjL <> => #()
     | InjR "m" => "m"
     end) "val"
.

Local Definition make_def (mset : list (string*val)) : val :=
  λ: "v", InjL (#"NO TYPE IDS YET", "v", (struct.fields_val mset)).
Program Definition make := unseal (_:seal (@make_def)). Obligation 1. by eexists. Qed.
Definition make_unseal : make = _ := seal_eq _.

End goose_lang.
End interface.

(* method sets for primitive types are empty *)
Section mset.
Context `{ffi_syntax}.
Definition uint64__mset : list (string * val) := [].
Definition int__mset : list (string * val) := [].
Definition bool__mset : list (string * val) := [].
Definition string__mset : list (string * val) := [].
Definition slice__mset : list (string * val) := [].
Definition slice__mset_ptr : list (string * val) := [].
End mset.
