From stdpp Require Import fin_maps gmap.
From Perennial.goose_lang Require Import lang notation.

Notation MapConsV k v m := (InjRV (PairV (PairV (LitV (LitInt k)) v) m)).
Notation MapNilV def := (InjLV def).
Notation AllocMap v := (Alloc (MapNilV v)) (only parsing).

Section goose_lang.
Context {ext:ext_op}.
Local Coercion Var' (s:string) : expr := Var s.

Definition MapGet: val :=
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

Definition MapLen: val :=
  λ: "mref",
  (rec: "mapLen" "m" :=
     match: "m" with
       InjL <> => #0
     | InjR "kvm" =>
       let: "m2" := Snd "kvm" in
       #1 + "mapLen" "m2"
     end) (!"mref").

Definition MapInsert: val :=
  λ: "mref" "k" "v",
  "mref" <- InjR ("k", "v", !"mref").

Definition MapDelete': val :=
  λ: "mv" "k",
  (rec: "mapDel" "m" :=
  match: "m" with
    InjL "def" => InjL "def"
  | InjR "kvm" =>
    let: "kv" := Fst "kvm" in
    let: "m2" := Snd "kvm" in
    if: "k" = (Fst "kv") then ("mapDel" "m2")
    else InjR ("kv", "mapDel" "m2")
  end) ("mv").

Definition MapDelete: val :=
  λ: "mref" "k",
  "mref" <- MapDelete' (!"mref") "k".

Definition mapGetDef: val :=
  rec: "mapGetDef" "m" :=
     match: "m" with
       InjL "def" => "def"
     | InjR "kvm" =>
       "mapGetDef" (Snd "kvm")
     end.

Definition MapClear: val :=
  λ: "mref",
  let: "def" := mapGetDef !"mref" in
  "mref" <- InjL "def".

Definition MapIter: val :=
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
       "mapIter" "m_rest"
     end) "mv";;
  FinishRead "mref".

End goose_lang.
