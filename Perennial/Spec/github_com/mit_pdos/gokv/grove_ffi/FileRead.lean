/-
`github.com/mit-pdos/gokv/grove_ffi.FileRead`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.gokv.grove_ffi.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std grove_ext

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.gokv.grove_ffi.Assumptions]

/-- `FileRead(f)`, for a valid file name `f`: a new slice holding the contents of file `f`, a
logically atomic spec. -/
abbrev github_com.mit_pdos.gokv.grove_ffi.FileRead.spec : Prop :=
  ∀ (f : GoString), ValidFileName f →
  ⊢ ∀ Φ : val → IProp GF,
      (|={⊤,∅}=> ∃ (dq : DFrac) (c : List w8), f f↦{dq} c ∗
        (f f↦{dq} c ={∅,⊤}=∗
          ∀ s : GoSlice, s ↦* c -∗ ownSliceCap w8 s (DFrac.own 1) -∗ Φ #s)) -∗
      WP (App (Val (@! FileRead)) (Val #f)) {{ Φ }}

end spec

end Perennial
