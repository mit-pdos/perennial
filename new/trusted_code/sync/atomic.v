From New.golang Require Import defn.

Module atomic.
Section code.
Context `{ffi_syntax}.

Definition LoadUint64 : val :=
  λ: "addr", Load "addr".

Definition StoreUint64 : val :=
  λ: "addr" "val", AtomicStore "addr" "val".

Definition AddUint64 : val :=
  λ: "addr", #() #().

End code.
End atomic.
