From Perennial.new_goose_lang Require Import prelude.

Section code.
Context `{ffi_syntax}.
Local Coercion Var' s: expr := Var s.

(* FIXME: make everything in here opaque. *)

(* FIXME: want to expose a type, not descriptor *)
Definition Mutex : descriptor :=
  ["state" :: boolT]%struct
.
Axiom WaitGroup: descriptor.

Definition Mutex__Lock : val :=
  rec: "f" "m" :=
    if: Snd (CmpXchg (struct.fieldRef Mutex "state" "m") #false #true) then
      #()
    else
      "f" "m"
.
Definition Mutex__Unlock : val :=
  λ: "m", exception_do (do: CmpXchg (struct.fieldRef Mutex "state" "m") #true #false ;;; return: #())
.

Definition NewCond : val := λ: "m", ref "m".
Definition Cond__Wait : val := λ: "c", exception_do (do: Mutex__Unlock !"c" ;;; do: Mutex__Lock !"c").
Definition Cond__Broadcast : val := λ: "c", #().
Definition Cond__Signal: val := λ: "c", #().
Axiom WaitGroup__Add : val.
Axiom WaitGroup__Done : val.
Axiom WaitGroup__Wait : val.

End code.
