From New.golang.defn Require Import loop typing list dynamic_typing.

Module map.
(* FIXME: seal these functions *)
Section goose_lang.
Context {ext:ffi_syntax}.

Definition nil : val := #null.

(* This model stores the values of the map into single memory cells, even if they
are entire structs that would usually be laid out with one memory cell per
field.  This is fine because it is not observable by clients: all APIs are
by-value, there is no way to take a reference 'into' the map. *)
Definition insert : val :=
  λ: "mref" "k" "v",
  "mref" <- InjR ("k", "v", !"mref").

Definition get : val :=
  λ: "mref" "k",
  (rec: "mapGet" "m" :=
     match: "m" with
       InjL "def" => ("def", #false)
     | InjR "kvm" =>
       let: "kv" := Fst "kvm" in
       let: "m2" := Snd "kvm" in
       if: "k" = (Fst "kv") then (Snd "kv", #true)
       else "mapGet" "m2"
     end) (!"mref").

Definition delete_aux : val :=
  rec: "mapDel" "m" "k" :=
    match: "m" with
      InjL "def" => InjL "def"
    | InjR "kvm" =>
        let: "kv" := Fst "kvm" in
        let: "m2" := Snd "kvm" in
        if: "k" = (Fst "kv") then ("mapDel" "m2" "k")
        else InjR ("kv", "mapDel" "m2" "k")
    end
.

Definition delete : val := λ: "mref" "k", "mref" <- delete_aux (!"mref") "k".

Definition for_range : val :=
  λ: "mref" "body",
  let: "mv" := StartRead "mref" in
  (rec: "mapIter" "m" :=
     (* TODO: the iteration order should really be non-deterministic *)
     match: "m" with
       InjL "def" => #()
     | InjR "kvm" =>
       let: "k" := Fst (Fst "kvm") in
       let: "v" := Snd (Fst "kvm") in
       let: "m_rest" := Snd "kvm" in
       "body" "k" "v";;
       "mapIter" (delete_aux "m_rest" "k")
     end) "mv";;
  FinishRead "mref".

Definition len : val :=
  λ: "mref",
    let: "len" := Alloc #(W64 0) in
    for_range "mref" (λ: <> <>,
                       "len" <- !"len" + #(W64 1) ;;
                       (for: (!"len" < #(W64 (2^64-1))) ; Skip := #())) ;;
    !"len".

(* key type is also supplied to supply a type to the wp lemma *)
Definition make : val :=
  λ: "kt" "vt", Alloc (InjL (type.zero_val "vt")).

(* TODO: this produces a map value and doesn't allocate a reference *)
Definition literal : val :=
  λ: "kt" "vt",
  rec: "literal" "alist" :=
    list.Match "alist"
      (λ: <>, InjL (type.zero_val "vt"))
      (λ: "kv" "alist", InjR ("kv", ("literal" "alist")))
.

End goose_lang.
End map.

Global Opaque map.insert map.get map.delete map.for_range map.len map.make.
