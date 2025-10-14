From New.golang Require Import defn.

Module spinlock.
Section code.
Context `{ffi_syntax}.

Definition trylock : val :=
  λ: "m", Snd (CmpXchg "m" #false #true).

Definition lock : val :=
  rec: "lock" "m" :=
    if: Snd (CmpXchg "m" #false #true) then
      #()
    else
      "lock" "m".

Definition unlock : val :=
  λ: "m", exception_do (do: CmpXchg "m" #true #false ;;; return: #())
.
End code.
End spinlock.

#[global] Opaque spinlock.trylock spinlock.lock spinlock.unlock.
