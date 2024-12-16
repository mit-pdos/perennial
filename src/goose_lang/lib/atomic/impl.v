From Perennial.goose_lang Require Import notation typing typed_mem.impl.

(* this code is intended to be used qualified with the atomic module *)
Module atomic.
Section goose_lang.
Context {ext:ffi_syntax} {ext_ty: ext_types ext}.

(* these are not values so that they are Atomic *)

Definition LoadUint64 : expr → expr := Load.
Definition LoadUint32 : expr → expr := LoadUint64.
Definition StoreUint64 : expr → expr → expr := AtomicStore.
Definition StoreUint32 : expr → expr → expr := StoreUint64.
Definition CompareAndSwapUint64 : expr → expr → expr → expr := CmpXchg.
Definition CompareAndSwapUint32 : expr → expr → expr → expr := CompareAndSwapUint64.

(* the type arguments to these functions are passed since that's the GooseLang
calling convention. They are not needed in the model, since these operations
only load pointers, and we don't need to know what the shape of the referenced
data is to write the model. *)
Definition Pointer__Load (_: ty) : expr → expr := Load.
Definition Pointer__Store (_: ty) : expr → expr → expr := AtomicStore.

End goose_lang.
End atomic.
