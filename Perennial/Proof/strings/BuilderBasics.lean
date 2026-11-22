/-
Shared definitions of the proofs of `strings.Builder`: `strings.ownBuilder l s`, a `*Builder`
that has accumulated the string `s`.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace strings

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- **The `*Builder` at `l` has accumulated the string `s`** (exclusive). Its buffer `buf` holds
`s`, at some fraction `dq` (`String` gives up part of it for good: the bytes a returned string
shares are never written again), and its spare capacity, fully (appends write there). Its `addr`
is `l` (it has been written to) or nil with an empty buffer (the zero value, or after `Reset`):
never another address, which is a copy by value and panics in `copyCheck`. -/
def ownBuilder (l : Loc) (s : GoString) : IProp GF :=
  iprop(∃ (b : Builder) (dq : DFrac), l ↦ b ∗ b.buf' ↦*{dq} s ∗
    ownSliceCap w8 b.buf' (DFrac.own 1) ∗
    ⌜✓ dq ∧ (b.addr' = l ∨ (b.addr' = null ∧ b.buf' = slice.nil))⌝)

/-- A zero `Builder` (`var b strings.Builder`) has accumulated `""`. -/
theorem ownBuilder_zero (l : Loc) :
    l ↦ (zero_val Builder) ⊢ ownBuilder (GF := GF) l [] := by
  iintro Hl
  unfold ownBuilder
  iexists (zero_val Builder), DFrac.own 1
  iframe Hl
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  ipureintro
  exact ⟨DFrac.valid_own_one, Or.inr ⟨rfl, rfl⟩⟩

end defs

end strings

end Perennial
