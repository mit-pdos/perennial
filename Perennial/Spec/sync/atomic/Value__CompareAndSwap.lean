/-
`sync.atomic.Value.CompareAndSwap`'s spec.
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

/-- `CompareAndSwap(nil, new)` on an empty cell owned by the caller; it may fail
spuriously (see the model). -/
abbrev sync.atomic.Value.CompareAndSwap.spec : Prop :=
  ∀ (u : Loc) (new : GoInterface),
  Aligned (.cell 16) (structFieldRef Value go!"v" u) →
  new ≠ interface.nil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗ ownValue u (DFrac.own 1) interface.nil }}
    (App (App (Val (u @!! go.GoType.PointerType Value.ty @!! go!"CompareAndSwap"))
      (Val #interface.nil)) (Val #new))
  {{ (b : Bool), RET #b; ownValue u (DFrac.own 1) (if b then new else interface.nil) }}

end spec

end Perennial
