/-
`sync.atomic.Value.Load`'s spec.
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

abbrev sync.atomic.Value.Load.spec : Prop :=
  ∀ (u : Loc) (dq : DFrac),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ x : GoInterface, ownValue u dq x ∗ (ownValue u dq x ={∅,⊤}=∗ Φ #x)) -∗
    WP (App (Val (u @!! go.GoType.PointerType Value.ty @!! go!"Load")) (Val #())) {{ Φ }}

end spec

end Perennial
