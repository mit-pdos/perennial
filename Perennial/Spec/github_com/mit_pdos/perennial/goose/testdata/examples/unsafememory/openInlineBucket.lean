/-
`openInlineBucket`'s spec (`goose/testdata/examples/unsafememory`).
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

/-- `openInlineBucket(value, writable)` opens the inline bucket whose bytes `value` holds: the header `bkt`, writable (a copy) if asked, and the page `rest` after it, both possibly in a copy of `value`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.openInlineBucket.spec : Prop :=
  ∀ (v : GoSlice) (bkt : InBucket) (rest : List w8) (writable : Bool),
    {{ (v ↦*□ (encode bkt ++ rest) ∗ ⌜rest ≠ []⌝ : IProp GF) }}
      (App (App (Val (@! openInlineBucket)) (Val #v)) (Val #writable))
    {{ (b ip : Loc), RET (PairV #b #ip);
       (if writable then b ↦ bkt else b ↦□ bkt) ∗ bytesPointsto ip DFrac.discard rest ∗
       ⌜0 < ip.addr⌝ }}

end spec

end Perennial
