/-
`crypto/sha1.block`'s spec.
-/
module

public import Perennial.Proof.crypto.sha1.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha1.Assumptions]

/-- `block(dig, p)` is `blockGeneric(dig, p)` (the build with `purego`). -/
abbrev crypto.sha1.block.spec : Prop :=
  ∀ (dig : Loc) (p : GoSlice) (dq : DFrac) (bs : List w8) (h : crypto.sha1.St),
    {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.sha1 ∗
       typedPointsto (structFieldRef crypto.sha1.digest go!"h" dig) (crypto.sha1.stArr h)
         (DFrac.own 1) ∗
       p ↦*{dq} bs }}
      (App (App (Val (@! crypto.sha1.block)) (Val #dig)) (Val #p))
    {{ RET #(); typedPointsto (structFieldRef crypto.sha1.digest go!"h" dig)
         (crypto.sha1.stArr (crypto.sha1.compressAll h bs)) (DFrac.own 1) ∗
       p ↦*{dq} bs }}

end spec

end Perennial
