/-
`sync.atomic.Uint32.CompareAndSwap`'s spec.
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

abbrev sync.atomic.Uint32.CompareAndSwap.spec : Prop :=
  ∀ (u : Loc) (old new : w32),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ (v : w32) (dq : DFrac), ownUint32 u dq v ∗
      ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
      (ownUint32 u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
    ⌜u ≠ null⌝ -∗
    WP (App (App (Val (u @!! go.GoType.PointerType Uint32.ty @!! go!"CompareAndSwap")) (Val #old))
      (Val #new)) {{ Φ }}

end spec

end Perennial
