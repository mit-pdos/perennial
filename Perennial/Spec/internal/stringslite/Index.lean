/-
`internal.stringslite.Index`'s spec.
-/
module

public import Perennial.Proof.internal.stringslite.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

/-- `stringslite.Index(s, substr)`: the first index of `substr` in `s`, or `-1` (`0` for an empty
`substr`). It reads `bytealg.MaxLen`, so it needs `bytealg` initialized (a dependency of this
package's `isPkgInit`). For a non-empty `substr` it evaluates `len(s)`, so `s` is a Go string's
length. -/
abbrev internal.stringslite.Index.spec : Prop :=
  ∀ (s substr : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.stringslite }}
      (App (App (Val (@! Index'')) (Val #s)) (Val #substr))
    {{ RET #(W64 (internal.bytealg.index s substr)); ⌜substr ≠ [] → s.length < 2 ^ 63⌝ }}

end spec

end Perennial
