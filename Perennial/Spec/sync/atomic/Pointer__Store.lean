/-
`sync.atomic.Pointer.Store`'s spec.
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

abbrev sync.atomic.Pointer.Store.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType) [IntoValTyped (GF := GF) T' T] (u : Loc) (v : Loc),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ old : Loc, ownPointer (T' := T') u (DFrac.own 1) old ∗
      (ownPointer (T' := T') u (DFrac.own 1) v ={∅,⊤}=∗ Φ #())) -∗
    WP (App (Val (u @!! go.GoType.PointerType (Pointer.ty T) @!! go!"Store")) (Val #v)) {{ Φ }}

end spec

end Perennial
