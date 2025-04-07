From Perennial.goose_lang Require Export notation typing.

Section goose_lang.
  Context {ext:ffi_syntax}.

  (* RWlock is a reference call containing a uint 64:
    - If value is 0, lock is write locked
    - If value is 1, lock is free
    - If value is n for n > 1, lock is read locked with (n-1) readers *)

  Definition newRWMutex : val := λ: <>, ref #1.

  Definition RWMutex__TryRLock : val :=
    λ: "l",
    let: "n" := ! "l" in
    if: (#1 ≤ "n") `and` ("n" < "n" + #1) then
      CAS "l" "n" ("n" + #1)
    else #false.

  Definition RWMutex__RLock : val :=
    rec: "RWMutex__RLock" "l" := if: RWMutex__TryRLock "l" then #() else "RWMutex__RLock" "l".

  (* TODO: RWMutex__TryRUnlock isn't there in actual Golang API. *)
  Definition RWMutex__TryRUnlock : val :=
    λ: "l",
    let: "n" := ! "l" in
    if: (#1 < "n") then
      CAS "l" "n" ("n" - #1)
    else #false.

  Definition RWMutex__RUnlock : val :=
    rec: "RWMutex__RUnlock" "l" := if: RWMutex__TryRUnlock "l" then #() else "RWMutex__RUnlock" "l".

  Definition RWMutex__TryLock : val :=
    λ: "l", CAS "l" #1 #0.

  Definition RWMutex__Lock : val :=
    rec: "RWMutex__Lock" "l" := if: RWMutex__TryLock "l" then #() else "RWMutex__Lock" "l".

  Definition RWMutex__Unlock : val := λ: "l", CmpXchg "l" #0 #1;; #().

End goose_lang.
