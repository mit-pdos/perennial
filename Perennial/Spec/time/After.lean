/-
`time.After`'s spec.
-/
module

public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `time.After(d)`: a channel on which a receive may yield some time, which comes only once the
runtime clock has reached `T + d`, for `T` the clock's reading at the call, at least any bound
`clockLb n` the caller holds (`time.clockLb`, `Proof/time/Base.lean`). Each value carries `Ψ T`,
for the `Ψ` the caller chooses and derives from `clockLb (T + d)` (the wand, used once, by the
goroutine that sends). For any `d` (a non-positive one: the clock has already reached `T + d`). -/
abbrev time.After.spec : Prop :=
  ∀ (d : time.Duration) (n : Int) (Ψ : Int → IProp GF),
    {{ time.clockLb n ∗ (∀ T : Int, ⌜n ≤ T⌝ -∗ time.clockLb (T + sint.Z d) -∗ Ψ T) }}
      (App (Val (@! time.After)) (Val #d))
    {{ (ch : Loc) (γ : ChanNames) (T : Int), RET #ch; ⌜n ≤ T⌝ ∗ time.clockLb T ∗
        isChanBag γ ch (V := time.Time) (fun _ => Ψ T) }}

/-- `time.After(d)` for a caller that needs nothing of the clock: under the package's `isPkgInit`
(which gives the clock's first bound, `isPkgInit_clockLb`), a channel on which a receive may yield
some time (a bag of times, with no logical content). -/
theorem time.After.spec_pkgInit (wp_After : time.After.spec (GF := GF) (hG := hG))
    (d : time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
      (App (Val (@! time.After)) (Val #d))
    {{ (ch : Loc) (γ : ChanNames), RET #ch;
        isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }} := by
  wp_start_folded
  ihave #Hlb : time.clockLb (GF := GF) (-2 ^ 63) $$ []
  · iapply time.isPkgInit_clockLb $$ Hpkg
  wp_apply wp_After d (-2 ^ 63) (fun _ => iprop(True)) $$ [] as %ch %γ %T ⟨-, -, #Hch⟩
  · iframe Hlb
    iintro %T _ _
    itrivial
  iapply HΦ
  iexact Hch

end spec

end Perennial
