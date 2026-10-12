/-
`sort.Find`'s spec.
-/
module

public import Perennial.Proof.sort.FindBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- `sort.Find(n, cmp)`: binary search for the least `i ∈ [0, n)` with `cmp i ≤ 0`, for a `cmp`
that goes from positive to zero to negative on `[0, n)` (`IsMonoCmp`); `found` says whether `cmp
i = 0`. See `FindBasics.lean`. -/
abbrev sort.Find.spec : Prop :=
  ∀ (n : w64) (cmp_code : GoFunc) (cmp : Int → Int) (I : IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        ⌜0 ≤ sint.Z n⌝ ∗
        cmpImplements cmp_code cmp (sint.Z n) I ∗
        I ∗
        ⌜IsMonoCmp cmp (sint.Z n)⌝ }}
      (App (App (Val (@! Find)) (Val #n)) (Val #cmp_code))
    {{ (i : w64) (found : Bool), RET (PairV #i #found);
        I ∗
        ⌜found = true ↔ sint.Z i < sint.Z n ∧ cmp (sint.Z i) = 0⌝ ∗
        ⌜(∀ i, 0 ≤ i ∧ i < sint.Z n → cmp i > 0) → sint.Z i = sint.Z n⌝ ∗
        ⌜∀ k, 0 ≤ k ∧ k < sint.Z i → cmp k > 0⌝ }}

end spec

end Perennial
