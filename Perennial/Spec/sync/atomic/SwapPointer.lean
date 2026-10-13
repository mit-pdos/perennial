/-
`sync.atomic.SwapPointer`'s spec.
-/
module

public import Perennial.Proof.sync.atomic.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

abbrev sync.atomic.SwapPointer.spec : Prop :=
  ∀ (addr : Loc) (v : Loc), Aligned (.cell 8) addr →
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ oldv : Loc, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #oldv)) -∗
    WP (App (App (Val (@! SwapPointer)) (Val #addr)) (Val #v)) {{ Φ }}

end spec

end Perennial
