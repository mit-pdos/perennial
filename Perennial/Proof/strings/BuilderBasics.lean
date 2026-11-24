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

/-- **The field `addr` of the `*Builder` at `l`**: nil, and owned, while the Builder has not been
written to (`used = false`); `l` once it has (`used = true`), persistently: `copyCheck`'s model
leaves a reader on the field for good (`gomodel.StartRead(&b.addr)`), so nothing stores to it again
(`goose/model/overlay/strings/builder.go`, `copyCheck`). -/
def ownBuilderAddr (l : Loc) (used : Bool) : IProp GF :=
  if used then typedPointsto (structFieldRef Builder go!"addr" l) l DFrac.discard
  else typedPointsto (structFieldRef Builder go!"addr" l) null (DFrac.own 1)

/-- **The `*Builder` at `l` has accumulated the string `s`** (exclusive). Its field `addr` is
`ownBuilderAddr`; its buffer `buf` holds `s`, at some fraction `dq` (`String` gives up part of it
for good: the bytes a returned string shares are never written again), and its spare capacity,
fully (appends write there). There is no points-to of the whole struct: once used, the Builder
cannot be copied by value with its `addr` and stored back (that store is stuck in the model). -/
def ownBuilder (l : Loc) (s : GoString) : IProp GF :=
  iprop(∃ (used : Bool) (buf : GoSlice) (dq : DFrac), ⌜l ≠ null⌝ ∗ ownBuilderAddr l used ∗
    typedPointsto (structFieldRef Builder go!"buf" l) buf (DFrac.own 1) ∗ buf ↦*{dq} s ∗
    ownSliceCap w8 buf (DFrac.own 1) ∗ ⌜✓ dq⌝)

/-- A zero `Builder` (`var b strings.Builder`) has accumulated `""`. -/
theorem ownBuilder_zero (l : Loc) :
    l ↦ (zero_val Builder) ⊢ ownBuilder (GF := GF) l [] := by
  iintro Hl
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  iStructNamed Hl
  unfold ownBuilder ownBuilderAddr
  iexists false, slice.nil, DFrac.own 1
  simp only [Bool.false_eq_true, ↓reduceIte]
  isplitr
  · ipureintro; exact Hnn
  iframe addr buf
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  ipureintro
  exact DFrac.valid_own_one

end defs

end strings

end Perennial
