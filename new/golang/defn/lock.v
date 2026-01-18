From New.golang Require Import defn.pre.

Module lock.
Section code.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.

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
End lock.

#[global] Opaque lock.trylock lock.lock lock.unlock.
