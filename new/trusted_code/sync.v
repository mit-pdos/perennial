From New.golang Require Import defn.

Module sync.
Module Mutex. Definition id : go_string := "sync.Mutex". End Mutex.
Module Cond. Definition id : go_string := "sync.Cond". End Cond.

Section code.
Context `{ffi_syntax}.

(* FIXME: make everything in here opaque. *)

Definition Mutex : go_type := structT [
    "state" :: boolT
  ].

Definition Mutex__TryLockⁱᵐᵖˡ : val :=
  λ: "m" <>, Snd (CmpXchg (struct.field_ref Mutex "state"%go "m") #false #true).

Definition Mutex__Lockⁱᵐᵖˡ : val :=
  λ: "m" <>,
    if: Snd (CmpXchg (struct.field_ref Mutex "state"%go "m") #false #true) then
      #()
    else
      method_call #(ptrT.id Mutex.id) #"Lock" "m" #().

Definition Mutex__Unlockⁱᵐᵖˡ : val :=
  λ: "m" <>, exception_do (do: CmpXchg (struct.field_ref Mutex "state"%go "m") #true #false ;;; return: #())
.

Definition Cond : go_type := structT [
    "L" :: interfaceT
  ].

Definition NewCondⁱᵐᵖˡ : val := λ: "m", let: "x" := mem.alloc Cond in
                                        "x" <-[Cond] (struct.make Cond [{ (#"L", "m") }]);;
                                        "x".
Definition Cond__Waitⁱᵐᵖˡ : val := λ: "c" <>, exception_do (
                                 do: interface.get #"Unlock"%go (![interfaceT] (struct.field_ref Cond "L"%go "c")) #() ;;;
                                 do: interface.get #"Lock"%go (![interfaceT] (struct.field_ref Cond "L"%go "c")) #()
                               ).
Definition Cond__Broadcastⁱᵐᵖˡ : val := λ: "c" <>, #().
Definition Cond__Signalⁱᵐᵖˡ : val := λ: "c" <>, #().

Definition runtime_Semacquireⁱᵐᵖˡ : val :=
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
    ).

Definition runtime_Semreleaseⁱᵐᵖˡ : val :=
  λ: "addr" "_handoff" "_skipframes", AtomicOp PlusOp "addr" #(W32 1);; #().

(* differs from runtime_Semacquire only in the park "reason", used for internal
   concurrency testing *)
Definition runtime_SemacquireWaitGroupⁱᵐᵖˡ : val :=
  λ: "addr" "_synctestDurable", func_call #"sync.runtime_Semacquire" "addr".

Definition runtime_SemacquireRWMutexRⁱᵐᵖˡ : val :=
  λ: "addr" "_lifo" "_skipframes", func_call #"sync.runtime_Semacquire" "addr".

Definition runtime_SemacquireRWMutexⁱᵐᵖˡ : val :=
  λ: "addr" "_lifo" "_skipframes", func_call #"sync.runtime_Semacquire" "addr".

End code.
End sync.
