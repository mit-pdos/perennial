From Perennial.go_lang Require Export
     lang notation slice map struct typing.

(* We provide stubs here for primitive operations to make the Goose unit tests
   compile. *)

(* TODO: replace all of these stubs with real operations *)

Inductive LockMode := Reader | Writer.
Definition uint64_to_string {ext: ext_op}: val := λ: <>, #().

Module Data.
  Section go_lang.
    Context {ext:ext_op}.
    Definition stringToBytes: val := λ: <>, #().
    Definition bytesToString: val := λ: <>, #().
    Definition sliceAppendSlice: val := λ: <>, #().
    Definition mapAlter: val := λ: <>, #().
    Definition mapIter: val := λ: <>, #().
    Definition mapClear: val := λ: <>, #().
    Definition randomUint64: val := λ: <>, #().
    Definition newLock: val := λ: <>, #().
    Definition lockRelease (m: LockMode): val := λ: <>, #().
    Definition lockAcquire (m: LockMode): val := λ: <>, #().
  End go_lang.
End Data.

Module FS.
  Section go_lang.
    Context {ext:ext_op}.
    Definition atomicCreate: val := λ: <>, #().
  End go_lang.
End FS.
