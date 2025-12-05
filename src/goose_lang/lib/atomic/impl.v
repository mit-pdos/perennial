From Perennial.goose_lang Require Import notation typing typed_mem.impl.

(* this code is intended to be used qualified with the atomic module *)
Module atomic.
Section goose_lang.
Context {ext:ffi_syntax} {ext_ty: ext_types ext}.

(* these are not values so that they are Atomic *)

Definition LoadUint64 : expr → expr := Load.
Definition LoadUint32 : expr → expr := LoadUint64.
Definition SwapUint64 : expr → expr → expr := AtomicSwap.
Definition SwapUint32 : expr → expr → expr := SwapUint64.
Definition StoreUint64 : val :=
  λ: "l" "v", SwapUint64 "l" "v";; #().
Definition StoreUint32 : val :=
  λ: "l" "v", SwapUint32 "l" "v";; #().
Definition CompareAndSwapUint64 : expr → expr → expr → expr := CmpXchg.
Definition CompareAndSwapUint32 : expr → expr → expr → expr := CompareAndSwapUint64.

(* the type arguments to these functions are passed since that's the GooseLang
calling convention. They are not needed in the model, since these operations
only load pointers, and we don't need to know what the shape of the referenced
data is to write the model. *)
Definition Pointer__Load (_: ty) : expr → expr := Load.
Definition Pointer__Swap (_: ty) : expr → expr → expr := AtomicSwap.
Definition Pointer__Store (t: ty) : val :=
  λ: "l" "v", Pointer__Swap t "l" "v";; #().

End goose_lang.
End atomic.
