/-
`workq.wordCount`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

/-- `wordCount(docs)`, for fewer than `2^32` documents (the model's `make(chan T, n)` is stuck for
`n ≥ 2^32`, where Go may panic: `chan.wp_make2`). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.wordCount.spec : Prop :=
  ∀ (docs_sl : GoSlice) (docs : List GoString),
  docs.length < 2 ^ 32 →
    {{ isPkgInit (PROP := IProp GF) pkg ∗ "Hdocs" ∷ docs_sl ↦* docs }}
      (App (Val (@! wordCount)) (Val #docs_sl))
    {{ RET #(W64 ((docs.map word_count).sum : Int)); True }}

end spec

end Perennial
