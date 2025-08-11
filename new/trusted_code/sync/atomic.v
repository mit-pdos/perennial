From New.golang Require Import defn.

Module atomic.
Section code.
Context `{ffi_syntax}.

Definition LoadUint64ⁱᵐᵖˡ : val :=
  λ: "addr", Load "addr".

Definition StoreUint64ⁱᵐᵖˡ : val :=
  λ: "addr" "val", AtomicStore "addr" "val".

Definition AddUint64ⁱᵐᵖˡ : val :=
  λ: "addr" "val", AtomicOp PlusOp "addr" "val".

Definition CompareAndSwapUint64ⁱᵐᵖˡ : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new").

Definition LoadInt32ⁱᵐᵖˡ : val :=
  λ: "addr", Load "addr".

Definition StoreInt32ⁱᵐᵖˡ : val :=
  λ: "addr" "val", AtomicStore "addr" "val".

Definition AddInt32ⁱᵐᵖˡ : val :=
  λ: "addr" "val", AtomicOp PlusOp "addr" "val".

Definition CompareAndSwapInt32ⁱᵐᵖˡ : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new").

End code.
End atomic.
