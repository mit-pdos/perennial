/-
`github.com/goose-lang/std/std_core.Shuffle`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.std.std_core.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

/-- `Shuffle(s)`: permutes the elements of `s` in place. -/
abbrev github_com.goose_lang.std.std_core.Shuffle.spec : Prop :=
  ∀ (s : GoSlice) (xs : List w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core ∗ s ↦* xs }}
      (App (Val (@! Shuffle)) (Val #s))
    {{ (xs' : List w64), RET #(); ⌜xs ≡ₚ xs'⌝ ∗ s ↦* xs' }}

end spec

end Perennial
