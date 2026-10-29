/-
`writeInlineBucket`'s spec (`goose/testdata/examples/unsafememory`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Pages

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Assumptions]

/-- `writeInlineBucket(b, inodes)` is a new slice holding the bucket header `*b` followed by a leaf page holding `ms`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInlineBucket.spec : Prop :=
  ∀ (b : Loc) (bkt : InBucket) (dq : DFrac) (s : GoSlice) (ms : List InodeM),
    {{ (b ↦{dq} bkt ∗ inodesOwn s ms ∗ ⌜pageFits ms⌝ : IProp GF) }}
      (App (App (Val (@! writeInlineBucket)) (Val #b)) (Val #s))
    {{ (v : GoSlice), RET #v; b ↦{dq} bkt ∗
       v ↦* (encode bkt ++ encode (leafHeader ms) ++ pageBody true ms) }}

end spec

end Perennial
