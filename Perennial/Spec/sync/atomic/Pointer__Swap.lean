/-
`sync.atomic.Pointer.Swap`'s spec.
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

abbrev sync.atomic.Pointer.Swap.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType) [IntoValTyped (GF := GF) T' T] (u : Loc) (v' : Loc),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ∃ v : Loc, ownPointer (T' := T') u (DFrac.own 1) v ∗
      (ownPointer (T' := T') u (DFrac.own 1) v' ={∅,⊤}=∗ Φ #v)) -∗
    WP (App (Val (u @!! go.GoType.PointerType (Pointer.ty T) @!! go!"Swap")) (Val #v')) {{ Φ }}

end spec

end Perennial
