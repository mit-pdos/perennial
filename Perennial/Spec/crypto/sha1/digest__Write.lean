/-
`crypto/sha1.(*digest).Write`'s spec.
-/
module

public import Perennial.Proof.crypto.sha1.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha1.Assumptions]

/-- `d.Write(p)` of a digest that has absorbed `m` absorbs `p`, and returns `len(p)` and `nil`, when the `fips140` setting is not `only` (in mode `only` it returns an error). -/
abbrev crypto.sha1.digest.Write.spec : Prop :=
  ∀ (d : Loc) (v : crypto.sha1.digest) (m : List w8) (p : GoSlice) (dq : DFrac) (bs : List w8),
    crypto.fips140.GodebugFips140Off →
    crypto.sha1.absorbed v m →
    {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.sha1 ∗ d ↦ v ∗ p ↦*{dq} bs }}
      (App (Val (d @!! go.GoType.PointerType crypto.sha1.digest.ty @!! go!"Write")) (Val #p))
    {{ RET (PairV #(W64 (bs.length : Int)) #interface.nil);
        ∃ v' : crypto.sha1.digest, d ↦ v' ∗ ⌜crypto.sha1.absorbed v' (m ++ bs)⌝ ∗ p ↦*{dq} bs }}

end spec

end Perennial
