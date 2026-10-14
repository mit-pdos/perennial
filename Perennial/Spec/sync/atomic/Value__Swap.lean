/-
`sync.atomic.Value.Swap`'s spec.
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

abbrev sync.atomic.Value.Swap.spec : Prop :=
  ∀ (u : Loc) (v : GoInterface),
  v ≠ interface.nil →
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ (ownValue u (DFrac.own 1) interface.nil ∗
      (ownValue u (DFrac.own 1) v ={∅,⊤}=∗ Φ #interface.nil))) -∗
    WP (App (Val (u @!! go.GoType.PointerType Value.ty @!! go!"Swap")) (Val #v)) {{ Φ }}

end spec

end Perennial
