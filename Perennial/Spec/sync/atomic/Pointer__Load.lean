/-
`sync.atomic.Pointer.Load`'s spec.
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

abbrev sync.atomic.Pointer.Load.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType) [IntoValTyped (GF := GF) T' T]
    [go.Reinterpretable T] (u : Loc) (dq : DFrac),
  ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
    (|={⊤,∅}=> ▷ ∃ v : Loc, ownPointer (T' := T') u dq v ∗ (ownPointer (T' := T') u dq v ={∅,⊤}=∗ Φ #v)) -∗
    ⌜u ≠ null⌝ -∗ ⌜Aligned (.cell 8) (structFieldRef (Pointer T') go!"v" u)⌝ -∗
    WP (App (Val (u @!! go.GoType.PointerType (Pointer.ty T) @!! go!"Load")) (Val #())) {{ Φ }}

end spec

end Perennial
