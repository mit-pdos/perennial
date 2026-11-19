/-
`crypto/sha256.Sum256`'s spec.
-/
module

public import Perennial.Proof.crypto.sha256.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] {ok : Sha256Filter} [HasSha256 ok]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha256.Assumptions]

/-- `Sum256(data)`: with read access (any fraction `dq`) to the slice `s` holding `data`,
returns a 32-byte array `h` that is `data`'s hash, the slice unchanged. -/
abbrev crypto.sha256.Sum256.spec : Prop :=
  ∀ (s : GoSlice) (data : List w8) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.sha256 ∗ s ↦*{dq} data }}
      (App (Val (@! crypto.sha256.Sum256)) (Val #s))
    {{ (h : GoArray w8 32), RET #h;
        s ↦*{dq} data ∗ crypto.sha256.is_hash (GF := GF) data h }}

end spec

end Perennial
