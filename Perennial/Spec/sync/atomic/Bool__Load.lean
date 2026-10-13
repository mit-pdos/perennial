/-
`sync.atomic.Bool.Load`'s spec.
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

abbrev sync.atomic.Bool.Load.spec : Prop :=
  ∀ (u : Loc) (dq : DFrac),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ v : Bool, ownBool u dq v ∗ (ownBool u dq v ={∅,⊤}=∗ Φ #v)) -∗
    ⌜u ≠ null⌝ -∗ ⌜Aligned (.word 4) (structFieldRef Bool' go!"v" u)⌝ -∗
    WP (App (Val (u @!! go.GoType.PointerType Bool'.ty @!! go!"Load")) (Val #())) {{ Φ }}

end spec

end Perennial
