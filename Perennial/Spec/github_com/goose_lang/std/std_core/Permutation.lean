/-
`github.com/goose-lang/std/std_core.Permutation`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

/-- `Permutation(n)`: a new slice holding a permutation of `0, …, n-1`. `make` panics when
the slice has more than `2^48` bytes, so `n ≤ 2^45`. -/
abbrev github_com.goose_lang.std.std_core.Permutation.spec : Prop :=
  ∀ (n : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.std.std_core ∗ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 2 ^ 45⌝ }}
      (App (Val (@! Permutation)) (Val #n))
    {{ (xs : List w64) (s : GoSlice), RET #s;
        ⌜xs ≡ₚ (seqZ 0 (sint.Z n)).map (fun z => W64 z)⌝ ∗ s ↦* xs }}

end spec

end Perennial
