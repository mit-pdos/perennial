From New.golang Require Import defn.

Module sync.
Section code.
Context `{ffi_syntax}.

Definition pkg_name' : go_string := "sync".

(* FIXME: make everything in here opaque. *)

Definition Mutex : go_type := structT [
    "state" :: boolT
  ].

Definition Mutex__TryLock : val :=
  λ: "m" <>, Snd (CmpXchg (struct.field_ref Mutex "state" "m") #false #true).

Definition Mutex__Lock : val :=
  λ: "m" <>,
    if: Snd (CmpXchg (struct.field_ref Mutex "state" "m") #false #true) then
      #()
    else
      method_call #pkg_name' #"Mutex'ptr" #"Lock" "m" #().

Definition Mutex__Unlock : val :=
  λ: "m" <>, exception_do (do: CmpXchg (struct.field_ref Mutex "state" "m") #true #false ;;; return: #())
.

Definition Cond : go_type := structT [
    "L" :: interfaceT
  ].

Definition NewCond : val := λ: "m", ref_ty Cond (struct.make Cond [{ (#"L", "m") }]).
Definition Cond__Wait : val := λ: "c" <>, exception_do (
                                 do: interface.get #"Unlock"%go (![interfaceT] (struct.field_ref Cond "L" "c")) #() ;;;
                                 do: interface.get #"Lock"%go (![interfaceT] (struct.field_ref Cond "L" "c")) #()
                               ).
Definition Cond__Broadcast : val := λ: "c" <>, #().
Definition Cond__Signal : val := λ: "c" <>, #().

Definition runtime_Semacquire : val :=
  (* inspired by runtime/sema.go:272:
     ```
     func cansemacquire(addr *uint32) bool {
        for {
            v := atomic.Load(addr)
            if v == 0 {
                return false
            }
            if atomic.Cas(addr, v, v-1) {
                return true
            }
        }
    }
    ```
*)
  λ: "addr", exception_do
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
       let: "v" := Load "addr" in
       (if: "v" = #(W32 0) then
          continue: #()
        else
          do: #()
       ) ;;;
       (if: Snd (CmpXchg "addr" "v" ("v" - #(W32 1))) then
          return: #()
        else
          do: #())
    )
.

Definition runtime_Semrelease : val :=
  λ: <>, #() #(). (* FIXME: use `AtomicAdd` *)

End code.
End sync.
