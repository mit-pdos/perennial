/-
`crypto/rand.Int`'s spec.
-/
module

public import Perennial.Proof.crypto.rand.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.rand.Assumptions]

/-- `crypto/rand.Int(rand.Reader, max)` returns a value in `[0, max)`, and no error, for
`0 < max < 2^63`. The bound on `max` is the range the model of `Int`
(`Perennial/TrustedCode/crypto/rand.lean`) covers; the reader is the package's own, which
never returns an error. -/
abbrev crypto.rand.Int.spec : Prop :=
  ∀ (rdr : GoInterface) (max : Loc) (mz : _root_.Int), 0 < mz ∧ mz < 2 ^ 63 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.rand ∗
       globalAddr Reader ↦□ rdr ∗ math.big.ownInt max mz }}
      (App (App (Val (@! Int')) (Val #rdr)) (Val #max))
    {{ (v : Loc) (z : _root_.Int), RET (PairV #v #interface.nil);
       math.big.ownInt max mz ∗ math.big.ownInt v z ∗ ⌜0 ≤ z ∧ z < mz⌝ }}

end spec

end Perennial
