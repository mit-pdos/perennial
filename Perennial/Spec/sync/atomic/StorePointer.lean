/-
`sync.atomic.StorePointer`'s spec.
-/
module

public import Perennial.Proof.sync.atomic.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

abbrev sync.atomic.StorePointer.spec : Prop :=
  ∀ (addr : Loc) (v : Loc),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ oldv : Loc, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
    WP (App (App (Val (@! StorePointer)) (Val #addr)) (Val #v)) {{ Φ }}

end spec

end Perennial
