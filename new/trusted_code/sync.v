From New.golang Require Import defn defn.lock.

Module sync.
Module Mutex. Definition id : go_string := "sync.Mutex". End Mutex.

Section code.
Context `{ffi_syntax}.

(* FIXME: make everything in here opaque. *)

Definition Mutex : go_type := structT [
    "state" :: boolT
  ].


Definition Mutex__TryLockⁱᵐᵖˡ : val :=
  λ: "m" <>, lock.trylock (struct.field_ref #Mutex #"state"%go "m").

Definition Mutex__Lockⁱᵐᵖˡ : val :=
  λ: "m" <>,
     lock.lock (struct.field_ref #Mutex #"state"%go "m").

Definition Mutex__Unlockⁱᵐᵖˡ : val :=
  λ: "m" <>, lock.unlock (struct.field_ref #Mutex #"state"%go "m").

Definition runtime_notifyListAddⁱᵐᵖˡ : val :=
  λ: "l", u_to_w32 ArbitraryInt.
Definition runtime_notifyListWaitⁱᵐᵖˡ : val :=
  λ: "l" "t", #().
Definition runtime_notifyListNotifyAllⁱᵐᵖˡ : val :=
  λ: "l", #().
Definition runtime_notifyListNotifyOneⁱᵐᵖˡ : val :=
  λ: "l", #().
Definition runtime_notifyListCheckⁱᵐᵖˡ : val :=
  λ: "l", #().

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
  λ: "addr", func_call #"sync.runtime_Semacquire" "addr".

Definition runtime_SemacquireRWMutexRⁱᵐᵖˡ : val :=
  λ: "addr" "_lifo" "_skipframes", func_call #"sync.runtime_Semacquire" "addr".

Definition runtime_SemacquireRWMutexⁱᵐᵖˡ : val :=
  λ: "addr" "_lifo" "_skipframes", func_call #"sync.runtime_Semacquire" "addr".

End code.
End sync.
