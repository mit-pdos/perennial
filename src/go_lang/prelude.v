From Perennial.go_lang Require Export
     lang notation slice struct typing.

(* We provide stubs here for primitive operations to make the Goose unit tests
   compile. *)

(* TODO: replace all of these stubs with real operations *)

Inductive LockMode := Reader | Writer.
Definition uint64_to_string {ext: ext_op}: val := λ: <>, #().
Definition lockRefT := refT uint64T.

Module Data.
  Section go_lang.
    Context `{ext_ty:ext_types}.
    Definition stringToBytes: val := λ: <>, #().
    Definition bytesToString: val := λ: <>, #().
    Definition sliceAppendSlice: val := λ: <>, #().
    Definition mapAlter: val := λ: <>, #().
    Axiom mapIter: val.
    Axiom mapIter_t : forall vt, ⊢ mapIter : (mapT vt -> (uint64T -> vt -> unitT) -> unitT).
    Definition mapClear: val := λ: <>, #().
    Definition randomUint64: val := λ: <>, #().

    Definition newLock: val := λ: <>, ref #0.
    Theorem newLock_t: ⊢ newLock : (unitT -> lockRefT).
    Proof.
      typecheck.
    Qed.

    Definition lockRelease (m: LockMode): val := λ: <>, #().
    Theorem lockRelease_t m: ⊢ lockRelease m : (lockRefT -> unitT).
    Proof.
      typecheck.
    Qed.

    Definition lockAcquire (m: LockMode): val := λ: <>, #().
    Theorem lockAcquire_t m: ⊢ lockAcquire m : (lockRefT -> unitT).
    Proof.
      typecheck.
    Qed.
  End go_lang.
End Data.

Opaque Data.newLock Data.lockRelease Data.lockAcquire.
Hint Resolve Data.newLock_t Data.lockRelease_t Data.lockAcquire_t : types.
Hint Resolve Data.mapIter_t : types.

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
