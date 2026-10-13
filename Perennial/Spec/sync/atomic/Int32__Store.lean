/-
`sync.atomic.Int32.Store`'s spec.
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

abbrev sync.atomic.Int32.Store.spec : Prop :=
  ∀ (u : Loc) (v : w32),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ old : w32, ownInt32 u (DFrac.own 1) old ∗
      (ownInt32 u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
    ⌜u ≠ null⌝ -∗ ⌜Aligned (.word 4) (structFieldRef Int32 go!"v" u)⌝ -∗
    WP (App (Val (u @!! go.GoType.PointerType Int32.ty @!! go!"Store")) (Val #v)) {{ Φ }}

end spec

end Perennial
