/-
`sync.atomic.AddInt64`'s spec.
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

abbrev sync.atomic.AddInt64.spec : Prop :=
  ∀ (addr : Loc) (v : w64),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗
      (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
    WP (App (App (Val (@! AddInt64)) (Val #addr)) (Val #v)) {{ Φ }}

end spec

end Perennial
