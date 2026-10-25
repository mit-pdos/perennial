/-
`internal.strconv.ParseUint`'s spec.
-/
module

public import Perennial.Proof.internal.strconv.ParseUintBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

/-- `ParseUint(s, base, bitSize)` in a base between 2 and 36 and a bit size between 0 and 64 (0
meaning 64) returns what `parseUint` says (`parseOut`): the number `s` denotes and a nil error
when every byte is a digit below the base and the value fits in the bit size; else `0` and
`ErrSyntax` (an empty `s`, or a byte that is not such a digit before the value overflows), or the
maximum `2^bitSize - 1` and `ErrRange`. -/
abbrev internal.strconv.ParseUint.spec : Prop :=
  ∀ (s : GoString) (base bitSize : w64),
    2 ≤ sint.Z base → sint.Z base ≤ 36 → 0 ≤ sint.Z bitSize → sint.Z bitSize ≤ 64 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.strconv }}
      (App (App (App (Val (@! ParseUint)) (Val #s)) (Val #base)) (Val #bitSize))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
        ⌜internal.strconv.parseOut (internal.strconv.parseUint s (sint.nat base) (sint.nat bitSize))
          (2 ^ internal.strconv.effBitSize (sint.nat bitSize) - 1) x err⌝ }}

end spec

end Perennial
