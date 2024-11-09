From Perennial.goose_lang Require Import notation.

(* this code is intended to be used qualified with the atomic module *)
Module atomic.
Section goose_lang.
Context {ext:ffi_syntax}.

Definition LoadUint64 : val :=
  λ: "l", Load "l".

Definition LoadUint32 : val := LoadUint64.

Definition StoreUint64 : val :=
  λ: "l" "x", AtomicStore "l" "x".

Definition StoreUint32 : val := StoreUint64.

Definition CompareAndSwapUint64 : val :=
  λ: "l" "old" "new", CmpXchg "l" "old" "new".

Definition CompareAndSwapUint32 : val := CompareAndSwapUint64.

End goose_lang.
End atomic.
