From Perennial.goose_lang Require Export notation typing.

Definition rwlockRefT {ext} {ext_ty: ext_types ext} := refT uint64T.

Module rwlock.
  Section goose_lang.
    Context {ext:ffi_syntax}.

    Local Coercion Var' (s:string): expr := Var s.

    (* RWlock is a reference call containing a uint 64:
      - If value is 0, lock is write locked
      - If value is 1, lock is free
      - If value is n for n > 1, lock is read locked with (n-1) readers *)

    Definition new: val := λ: <>, ref #1.

    Definition try_read_acquire : val :=
      λ: "l",
      let: "n" := ! "l" in
      if: (#1 ≤ "n") `and` ("n" < "n" + #1) then
        CAS "l" "n" ("n" + #1)
      else #false.

    Definition read_acquire : val :=
      rec: "acquire" "l" := if: try_read_acquire "l" then #() else "acquire" "l".

    Definition try_read_release : val :=
      λ: "l",
      let: "n" := ! "l" in
      if: (#1 < "n") then
        CAS "l" "n" ("n" - #1)
      else #false.

    Definition read_release : val :=
      rec: "release" "l" := if: try_read_release "l" then #() else "release" "l".

    Definition try_write_acquire : val :=
      λ: "l", CAS "l" #1 #0.

    Definition write_acquire : val :=
      rec: "acquire" "l" := if: try_write_acquire "l" then #() else "acquire" "l".
    Definition write_release : val := λ: "l", CmpXchg "l" #0 #1;; #().

  End goose_lang.
End rwlock.
