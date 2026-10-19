/-
`sync.atomic.Pointer.CompareAndSwap`'s spec.
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

abbrev sync.atomic.Pointer.CompareAndSwap.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType) [IntoValTyped (GF := GF) T' T] (u : Loc) (old new : Loc),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ (v : Loc) (dq : DFrac), ownPointer (T' := T') u dq v ∗
      ⌜dq = if v = old then DFrac.own 1 else dq⌝ ∗
      (ownPointer (T' := T') u dq (if v = old then new else v) ={∅,⊤}=∗ Φ #(decide (v = old)))) -∗
    WP (App (App (Val (u @!! go.GoType.PointerType (Pointer.ty T) @!! go!"CompareAndSwap")) (Val #old))
      (Val #new)) {{ Φ }}

end spec

end Perennial
