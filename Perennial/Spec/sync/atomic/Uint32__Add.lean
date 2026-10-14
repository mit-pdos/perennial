/-
`sync.atomic.Uint32.Add`'s spec.
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

abbrev sync.atomic.Uint32.Add.spec : Prop :=
  ∀ (u : Loc) (delta : w32),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ old : w32, ownUint32 u (DFrac.own 1) old ∗
      (ownUint32 u (DFrac.own 1) (old + delta) ={∅,⊤}=∗ Φ #(old + delta))) -∗
    WP (App (Val (u @!! go.GoType.PointerType Uint32.ty @!! go!"Add")) (Val #delta)) {{ Φ }}

end spec

end Perennial
