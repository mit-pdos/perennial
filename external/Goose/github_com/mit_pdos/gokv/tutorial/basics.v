(* autogenerated from github.com/mit-pdos/gokv/tutorial/basics *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Tracker := struct.decl [
  "mu" :: ptrT;
  "m" :: mapT uint64T
].

Definition Tracker__lookupLocked: val :=
  rec: "Tracker__lookupLocked" "t" "k" :=
    let: ("v", "ok") := MapGet (struct.loadF Tracker "m" "t") "k" in
    ("v", "ok").

Definition Tracker__registerLocked: val :=
  rec: "Tracker__registerLocked" "t" "k" "v" :=
    let: (<>, "ok") := Tracker__lookupLocked "t" "k" in
    (if: "ok"
    then #false
    else
      MapInsert (struct.loadF Tracker "m" "t") "k" "v";;
      #true).

Definition Tracker__Lookup: val :=
  rec: "Tracker__Lookup" "t" "k" :=
    lock.acquire (struct.loadF Tracker "mu" "t");;
    let: ("v", "ok") := Tracker__lookupLocked "t" "k" in
    lock.release (struct.loadF Tracker "mu" "t");;
    ("v", "ok").

Definition Tracker__Register: val :=
  rec: "Tracker__Register" "t" "k" "v" :=
    lock.acquire (struct.loadF Tracker "mu" "t");;
    let: "r" := Tracker__registerLocked "t" "k" "v" in
    lock.release (struct.loadF Tracker "mu" "t");;
    "r".

Definition MakeTracker: val :=
  rec: "MakeTracker" <> :=
    let: "t" := struct.alloc Tracker (zero_val (struct.t Tracker)) in
    struct.storeF Tracker "mu" "t" (lock.new #());;
    struct.storeF Tracker "m" "t" (NewMap uint64T uint64T #());;
    "t".

End code.
