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
    Definition open: val := λ: <>, #().
    Definition close: val := λ: <>, #().
    Definition list: val := λ: <>, #().
    Definition size: val := λ: <>, #().
    Definition readAt: val := λ: <>, #().
    Definition create: val := λ: <>, #().
    Definition append: val := λ: <>, #().
    Definition delete: val := λ: <>, #().
    Definition rename: val := λ: <>, #().
    Definition truncate: val := λ: <>, #().
    Definition atomicCreate: val := λ: <>, #().
    Definition link: val := λ: <>, #().
  End go_lang.
End FS.
Definition fileT: ty := unitT.

Module Globals.
  Section go_lang.
    Context {ext:ext_op}.
    Definition getX: val := λ: <>, #().
    Definition setX: val := λ: <>, #().
  End go_lang.
End Globals.

Definition lockRefT := refT intT.
