/-
`internal.bytealg.LastIndexByteString`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace internal.bytealg

/-- `LastIndexByteString`'s loop from `j` down: the last index below `j` of `c` in `s`, or `-1`. -/
def lastIdxFrom (s : List w8) (c : w8) : Nat → Int
  | 0 => -1
  | j + 1 => if s.getD j 0 = c then j else lastIdxFrom s c j

/-- The last index of `c` in `s`, or `-1`. -/
def lastIndexByte (s : List w8) (c : w8) : Int := lastIdxFrom s c s.length

theorem lastIdxFrom_bounds (s : List w8) (c : w8) (j : Nat) :
    -1 ≤ lastIdxFrom s c j ∧ lastIdxFrom s c j < j := by
  induction j with
  | zero => simp [lastIdxFrom]
  | succ k ih =>
    unfold lastIdxFrom
    split <;> omega

theorem lastIndexByte_bounds (s : List w8) (c : w8) :
    -1 ≤ lastIndexByte s c ∧ lastIndexByte s c < s.length :=
  lastIdxFrom_bounds s c s.length

end internal.bytealg

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.LastIndexByteString(s, c)`: the last index of `c` in `s`, or `-1`. It reads no
package variable, so it needs no initialized package. -/
abbrev internal.bytealg.LastIndexByteString.spec : Prop :=
  ∀ (s : GoString) (c : w8),
    {{ (True : IProp GF) }}
      (App (App (Val (@! LastIndexByteString)) (Val #s)) (Val #c))
    {{ RET #(W64 (internal.bytealg.lastIndexByte s c)); ⌜s.length < 2 ^ 63⌝ }}

end spec

end Perennial
