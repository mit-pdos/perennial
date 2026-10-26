/-
`sync.atomic.SwapInt64`'s spec.
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

abbrev sync.atomic.SwapInt64.spec : Prop :=
  ∀ (addr : Loc) (v : w64),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
    WP (App (App (Val (@! SwapInt64)) (Val #addr)) (Val #v)) {{ Φ }}

end spec

end Perennial
