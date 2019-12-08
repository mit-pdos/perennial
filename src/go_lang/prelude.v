From Perennial.go_lang Require Export
     lang notation slice map struct typing encoding.

(* We provide stubs here for primitive operations to make the Goose unit tests
   compile. *)

(* TODO: replace all of these stubs with real operations *)

Inductive LockMode := Reader | Writer.
Definition uint64_to_string {ext: ext_op}: val := λ: <>, #().
Definition lockRefT := refT uint64T.

Module Data.
  Section go_lang.
    Context `{ext_ty:ext_types}.
    Axiom stringToBytes: val.
    Axiom bytesToString: val.
    Axiom stringToBytes_t : ⊢ stringToBytes : (stringT -> slice.T byteT).
    Axiom bytesToString_t : ⊢ bytesToString : (slice.T byteT -> stringT).
    Definition randomUint64: val := λ: <>, #0.
    Theorem randomUint64_t: ⊢ randomUint64 : (unitT -> uint64T).
    Proof.
      typecheck.
    Qed.

    Definition newLock: val := λ: <>, ref #0.
    Theorem newLock_t: ⊢ newLock : (unitT -> lockRefT).
    Proof.
      type_step.
      type_step.
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

Hint Resolve Data.stringToBytes_t Data.bytesToString_t : types.

Opaque Data.randomUint64.
Hint Resolve Data.randomUint64_t : types.

Opaque Data.newLock Data.lockRelease Data.lockAcquire.
Hint Resolve Data.newLock_t Data.lockRelease_t Data.lockAcquire_t : types.

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
