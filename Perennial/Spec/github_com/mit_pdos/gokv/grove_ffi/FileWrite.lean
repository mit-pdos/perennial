/-
`github.com/mit-pdos/gokv/grove_ffi.FileWrite`'s spec.
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

/-- `FileWrite(f, data)`, for a valid file name `f`: file `f` now holds `data`, a logically
atomic spec; the data slice is only read. -/
abbrev github_com.mit_pdos.gokv.grove_ffi.FileWrite.spec : Prop :=
  ∀ (f : GoString) (s : GoSlice) (dq : DFrac) (data : List w8), ValidFileName f →
  ⊢ ∀ Φ : val → IProp GF, s ↦*{dq} data -∗
      (|={⊤,∅}=> ∃ old : List w8, f f↦ old ∗
        (f f↦ data ={∅,⊤}=∗ s ↦*{dq} data -∗ Φ #())) -∗
      WP (App (App (Val (@! FileWrite)) (Val #f)) (Val #s)) {{ Φ }}

end spec

end Perennial
