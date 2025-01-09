From New.golang Require Import defn.

Section code.
Context `{ffi_syntax}.

(* FIXME: make everything in here opaque. *)

Definition Mutex : go_type := structT [
    "state" :: boolT
  ]
.
Axiom WaitGroup: struct.descriptor.

Definition Mutex__TryLock : val :=
  λ: "m" <>, Snd (CmpXchg (struct.field_ref Mutex "state" "m") #false #true).
Definition Mutex__Lock : val :=
  rec: "f" "m" <> :=
    if: Snd (CmpXchg (struct.field_ref Mutex "state" "m") #false #true) then
      #()
    else
      "f" "m" #().
Definition Mutex__Unlock : val :=
  λ: "m" <>, exception_do (do: CmpXchg (struct.field_ref Mutex "state" "m") #true #false ;;; return: #())
.

Definition Mutex__mset : list (go_string * val) := [].

Definition Mutex__mset_ptr : list (go_string * val) := [
    ("TryLock"%go, Mutex__TryLock) ;
    ("Lock"%go, Mutex__Lock) ;
    ("Unlock"%go, Mutex__Unlock)
  ].

Definition NewCond : val := λ: "m", ref_ty interfaceT "m".
Definition Cond__Wait : val := λ: "c" <>, exception_do (
                                 do: interface.get "Unlock"%go (![interfaceT] "c") #() ;;;
                                 do: interface.get "Lock"%go (![interfaceT] "c") #()
                               ).
Definition Cond__Broadcast : val := λ: "c" <>, #().
Definition Cond__Signal: val := λ: "c" <>, #().
Axiom WaitGroup__Add : val.
Axiom WaitGroup__Done : val.
Axiom WaitGroup__Wait : val.

Definition initialize' : val := λ: <>, #().

End code.
