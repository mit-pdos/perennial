/-
`sort.Search`'s spec.
-/
module

public import Perennial.Proof.sort.SearchBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- `sort.Search(n, f)`: binary search for the least `i ∈ [0, n)` with `f i = true` (`n` if
there is none), for an `f` that goes from false to true on `[0, n)` (`IsMonoPred`). See
`SearchBasics.lean`. -/
abbrev sort.Search.spec : Prop :=
  ∀ (n : w64) (f_code : GoFunc) (f : Int → Bool) (I : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        ⌜0 ≤ sint.Z n⌝ ∗
        predImplements f_code f (sint.Z n) I ∗
        I ∗
        ⌜IsMonoPred f (sint.Z n)⌝ }}
      (App (App (Val (@! Search)) (Val #n)) (Val #f_code))
    {{ (i : w64), RET #i;
        I ∗
        ⌜0 ≤ sint.Z i⌝ ∗
        ⌜sint.Z i < sint.Z n → f (sint.Z i) = true⌝ ∗
        ⌜(∀ i, 0 ≤ i ∧ i < sint.Z n → f i = false) → sint.Z i = sint.Z n⌝ ∗
        ⌜∀ k, 0 ≤ k ∧ k < sint.Z i → f k = false⌝ }}

end spec

end Perennial
