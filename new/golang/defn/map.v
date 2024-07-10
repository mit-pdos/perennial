From Perennial.goose_lang Require Import notation.
From New.golang.defn Require Import loop typing.

Module map.
(* FIXME: seal these functions *)
Section goose_lang.
Context {ext:ffi_syntax}.
Local Coercion Var' (s:string) : expr := Var s.

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
        if: "k" = (Fst "kv") then ("mapDel" "m2")
        else InjR ("kv", "mapDel" "m2")
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

(* alternate implementation strategy - MapLen above was perhaps implemented when
the general proofs for map iteration weren't ready *)
Definition len : val :=
  λ: "mref",
    let: "len" := Alloc #0 in
    for_range "mref" (λ: <> <>,
                       "len" <- !"len" + #1 ;;
                       (for: (!"len" < #(2^64-1)) ; Skip := #())) ;;
    !"len".

Definition make (kt vt : go_type) : val :=
  λ: <>, Alloc (InjLV (zero_val vt)).

End goose_lang.
End map.
