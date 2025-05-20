From New.golang Require Import defn.

Module atomic.
Section code.
Context `{ffi_syntax}.

Definition LoadUint64 : val :=
  λ: "addr", Load "addr".

Definition StoreUint64 : val :=
  λ: "addr" "val", AtomicStore "addr" "val".

Definition AddUint64 : val :=
  λ: "addr" "val", AtomicOp PlusOp "addr" "val".

Definition CompareAndSwapUint64 : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new").

Definition LoadInt32 : val :=
  λ: "addr", Load "addr".

Definition StoreInt32 : val :=
  λ: "addr" "val", AtomicStore "addr" "val".

Definition AddInt32 : val :=
  λ: "addr" "val", AtomicOp PlusOp "addr" "val".

Definition CompareAndSwapInt32 : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new").

End code.
End atomic.
