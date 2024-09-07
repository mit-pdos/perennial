From Perennial.goose_lang Require Import notation.

Section goose_lang.
  Context {ext:ffi_syntax}.

  (* This models `&Mutex{}` in Go. It is lowercase since it does not correspond
  to a method from Go's sync package. *)
  Definition newMutex: val := λ: <>, ref #false.
  Definition Mutex__TryLock : val := λ: "l", CAS "l" #false #true.
  Definition Mutex__Lock : val :=
    rec: "acquire" "l" := if: Mutex__TryLock "l" then #() else "acquire" "l".
  Definition Mutex__Unlock : val := λ: "l", CmpXchg "l" #true #false;; #().

  Definition NewCond: val := λ: "l", ref "l".

  (* no-op in the model, only affects scheduling *)
  Definition Cond__Signal: val := λ: "l", #().
  Definition Cond__Broadcast: val := λ: "l", #().
  Definition Cond__Wait: val := λ: "l", Mutex__Unlock !"l";;
                                      (* actual cond var waits for a signal
                                          here, but the model does not take this
                                          into account *)
                                      Mutex__Lock !"l".
  Definition Cond__WaitTimeout: val := λ: "l" "timeout", Cond__Wait "l".

End goose_lang.

(* abbreviations for backwards compatibility

TODO: migrate all clients
*)
Module lock.
  Notation new := newMutex (only parsing).
  Notation try_acquire := Mutex__TryLock (only parsing).
  Notation acquire := Mutex__Lock (only parsing).
  Notation release := Mutex__Unlock (only parsing).
  Notation newCond := NewCond (only parsing).
  Notation condSignal := Cond__Signal (only parsing).
  Notation condBroadcast := Cond__Broadcast (only parsing).
  Notation condWait := Cond__Wait (only parsing).
  Notation condWaitTimeout := Cond__WaitTimeout (only parsing).
End lock.
