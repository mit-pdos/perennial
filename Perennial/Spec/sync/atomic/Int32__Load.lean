/-
`sync.atomic.Int32.Load`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

abbrev sync.atomic.Int32.Load.spec : Prop :=
  ∀ (u : Loc) (dq : DFrac),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ v : w32, ownInt32 u dq v ∗ (ownInt32 u dq v ={∅,⊤}=∗ Φ #v)) -∗
    WP (App (Val (u @!! go.GoType.PointerType Int32.ty @!! go!"Load")) (Val #())) {{ Φ }}

end spec

end Perennial
