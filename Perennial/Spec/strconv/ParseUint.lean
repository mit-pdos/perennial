/-
`strconv.ParseUint`'s spec.
-/
module

public import Perennial.Proof.strconv.Base
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
variable [package_sem : strconv.Assumptions]

/-- `strconv.ParseUint(s, base, bitSize)` in a base between 2 and 36 and a bit size between 0 and
64 (0 meaning 64): what `internal.strconv.parseUint` says. The number `s` denotes and a nil error,
when every byte of `s` is a digit below the base (`0`-`9`, then `a`-`z` or `A`-`Z`) and its
value fits in the bit size; else `0` and a fresh `*NumError{"ParseUint", s, ErrSyntax}` (an empty
`s`, or a byte that is not such a digit, before the value overflows), or the maximum
`2^bitSize - 1` and a `*NumError{"ParseUint", s, ErrRange}`. -/
abbrev strconv.ParseUint.spec : Prop :=
  ∀ (s : GoString) (base bitSize : w64),
    2 ≤ sint.Z base → sint.Z base ≤ 36 → 0 ≤ sint.Z bitSize → sint.Z bitSize ≤ 64 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (App (App (Val (@! ParseUint)) (Val #s)) (Val #base)) (Val #bitSize))
    {{ (x : w64) (err : GoInterface), RET (PairV #x #err);
        match internal.strconv.parseUint s (sint.nat base) (sint.nat bitSize) with
        | .ok n => ⌜x = W64 n ∧ err = interface.nil⌝
        | .errSyntax => ⌜x = W64 0⌝ ∗ strconv.numErrorOf err go!"ParseUint" s strconv.ErrSyntax
        | .errRange => ⌜x = W64 ((2 ^ internal.strconv.effBitSize (sint.nat bitSize) - 1 : Nat) : Int)⌝ ∗
            strconv.numErrorOf err go!"ParseUint" s strconv.ErrRange }}

end spec

end Perennial
