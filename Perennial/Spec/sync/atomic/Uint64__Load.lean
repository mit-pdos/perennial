/-
`sync.atomic.Uint64.Load`'s spec.
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

abbrev sync.atomic.Uint64.Load.spec : Prop :=
  ∀ (u : Loc) (dq : DFrac),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ v : w64, ownUint64 u dq v ∗ (ownUint64 u dq v ={∅,⊤}=∗ Φ #v)) -∗
    WP (App (Val (u @!! go.GoType.PointerType Uint64.ty @!! go!"Load")) (Val #())) {{ Φ }}

end spec

end Perennial
