/-
Persisting hypotheses.

`UpdateIntoPersistently P Q` says `P ⊢ |==> □ Q`. The `ipersist H` tactic
replaces a hypothesis `H : P` by a persistent `H : Q` (for instance a
`DFractional` points-to `l ↦{dq} v` becomes `l ↦□ v`).
-/
module

public import Iris.BI
public import Iris.ProofMode
public import Perennial.IrisLib.DFractional

@[expose] public section

namespace Perennial

open Iris Iris.BI

section ipersist
variable {PROP : Type _} [BI PROP] [BIUpdate PROP]

class UpdateIntoPersistently (P : PROP) (Q : outParam PROP) : Prop where
  update_into_persistently : P ⊢ |==> □ Q

export UpdateIntoPersistently (update_into_persistently)

set_option synthInstance.checkSynthOrder false in
/-- Used when `Q` is an output (produced by going from `P` to `Φ`). -/
instance dfractional_update_into_persistently (P : PROP) (Φ : DFrac → PROP) (dq : DFrac)
    [h : AsDFractional P Φ dq] [Affine (Φ .discard)] :
    UpdateIntoPersistently P (Φ .discard) where
  update_into_persistently := by
    have hd := h.as_dfractional_dfractional
    have := hd.dfractional_persistent
    refine h.as_dfractional.1.trans ((hd.dfractional_persist dq).trans (BIUpdate.mono ?_))
    exact intuitionistically_of_intuitionistic.2

/-- Used when `Q` is a fixed input. -/
theorem dfractional_update_into_persistently' (P Q : PROP) (Φ : DFrac → PROP) (dq : DFrac)
    [hP : AsDFractional P Φ dq] [Affine (Φ .discard)] (hQ : Q ⊣⊢ Φ .discard) :
    UpdateIntoPersistently P Q where
  update_into_persistently :=
    (dfractional_update_into_persistently P Φ dq).update_into_persistently.trans
      (BIUpdate.mono (intuitionistically_mono hQ.2))

theorem update_into_persistently_tac {P Q : PROP} (h : UpdateIntoPersistently P Q) :
    P ⊢ |==> □ Q :=
  h.update_into_persistently

end ipersist

/-- `ipersist H` turns the hypothesis `H : P` into a persistent hypothesis `H : Q`
using `UpdateIntoPersistently P Q`. The goal must allow
eliminating a basic update. -/
macro "ipersist " H:ident : tactic =>
  `(tactic| imod (update_into_persistently_tac (by exact inferInstance)) $$ $H:ident with #$H:ident)

end Perennial
