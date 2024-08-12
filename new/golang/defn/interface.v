From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import struct typing.

Module interface.
Section goose_lang.
Context `{ffi_syntax}.
Local Coercion Var' (s:string) : expr := Var s.

Definition get (f : string) : val :=
  λ: "v", let: (("typeid", "val"), "mset") := "v" in
          let: "mset" := (match: "mset" with InjL "v" => "v" | InjR <> => Panic "interface" end) in
          (match: (struct.assocl_lookup #(str f) "mset") with
            InjL <> => #()
            | InjR "m" => "m"
          end) (match: "val" with InjL "v" => "v" | InjR <> => Panic "interface" end)
.

Local Definition make_def (mset : list (string*val)) : val :=
  λ: "v", (#(str "NO TYPE IDS YET"), InjL "v", InjL (struct.fields_val mset)).
Program Definition make := unseal (_:seal (@make_def)). Obligation 1. by eexists. Qed.
Definition make_unseal : make = _ := seal_eq _.

End goose_lang.
End interface.

(* method sets for primitive types are empty *)
Section mset.
Context `{ffi_syntax}.
Definition uint64__mset : list (string * val) := [].
Definition string__mset : list (string * val) := [].
End mset.
