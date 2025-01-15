From New.golang Require Import defn.

Section code.
Context `{ffi_syntax}.

Definition pkg_name' : go_string := "sync".

(* FIXME: make everything in here opaque. *)

Definition Mutex : go_type := structT [
    "state" :: boolT
  ].

Definition Mutex' : (go_string * go_string) := (pkg_name', "Mutex"%go).
Definition Mutex'ptr : (go_string * go_string) := (pkg_name', "Mutex'ptr"%go).

Axiom WaitGroup : go_type.

Definition Mutex__TryLock' : val :=
  λ: "m" <>, Snd (CmpXchg (struct.field_ref Mutex "state" "m") #false #true).

Definition Mutex__Lock' : val :=
  rec: "f" "m" <> :=
    if: Snd (CmpXchg (struct.field_ref Mutex "state" "m") #false #true) then
      #()
    else
      "f" "m" #().
Definition Mutex__Unlock' : val :=
  λ: "m" <>, exception_do (do: CmpXchg (struct.field_ref Mutex "state" "m") #true #false ;;; return: #())
.

Definition Mutex'mset : list (go_string * val) := [].

Definition Mutex'ptr'mset : list (go_string * val) := [
    ("TryLock"%go, Mutex__TryLock') ;
    ("Lock"%go, Mutex__Lock') ;
    ("Unlock"%go, Mutex__Unlock')
  ].

Definition Cond : go_type := structT [
    "L" :: interfaceT
  ].

Definition NewCond : (go_string * go_string) := (pkg_name', "NewCond"%go).
Definition NewCond' : val := λ: "m", ref_ty Cond [{ (#"L", "m") }].
Definition Cond__Wait' : val := λ: "c" <>, exception_do (
                                 do: interface.get #"Unlock"%go (![interfaceT] (struct.field_ref Cond "L" "c")) #() ;;;
                                 do: interface.get #"Lock"%go (![interfaceT] (struct.field_ref Cond "L" "c")) #()
                               ).
Definition Cond__Broadcast' : val := λ: "c" <>, #().
Definition Cond__Signal': val := λ: "c" <>, #().

Definition Cond'mset : list (go_string * val) := [].

Definition Cond'ptr'mset : list (go_string * val) := [
    ("Broadcast"%go, Cond__Broadcast') ;
    ("Signal"%go, Cond__Signal') ;
    ("Wait"%go, Cond__Wait')
  ].

Axiom WaitGroup__Add' : val.
Axiom WaitGroup__Done' : val.
Axiom WaitGroup__Wait' : val.

Definition WaitGroup'mset : list (go_string * val) := [].

Definition WaitGroup'ptr'mset : list (go_string * val) := [
    ("Add"%go, WaitGroup__Add') ;
    ("Done"%go, WaitGroup__Done') ;
    ("Wait"%go, WaitGroup__Wait')
  ].

Definition msets' := [
    ("Mutex"%go, Mutex'mset);
    ("Mutex'ptr"%go, Mutex'ptr'mset)
  ].

Definition functions' :=  [
    ("NewCond"%go, NewCond')
  ].

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' [] functions' msets' (λ: <>,
      exception_do (do:  #())
      ).

End code.
