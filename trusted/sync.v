From Perennial.goose_lang.new Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

(* FIXME: make everything in here opaque. *)

(* FIXME: want to expose a type, not descriptor *)
Definition Mutex : descriptor :=
  ["state" :: boolT]%struct
.
Axiom WaitGroup: descriptor.

Definition Mutex__Lock : val :=
  rec: "f" "m" :=
    if: CmpXchg (struct.fieldRef Mutex "state" "m") #false #true then
      #()
    else
      "f" #()
.
Definition Mutex__Unlock : val :=
  λ: "f" "m", CmpXchg (struct.fieldRef Mutex "state" "m") #true #false
.

Definition NewCond : val := λ: "m", ref "m".
Definition Cond__Wait : val := λ: "c", exception_do (do: Mutex__Unlock !"c" ;;; do: Mutex__Lock !"c").
Definition Cond__Broadcast : val := λ: "c", #().
Definition Cond__Signal: val := λ: "c", #().
Axiom WaitGroup__Add : val.
Axiom WaitGroup__Done : val.
Axiom WaitGroup__Wait : val.

End code.
