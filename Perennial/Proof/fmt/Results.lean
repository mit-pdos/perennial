/-
Results of `fmt` derived from the linked ones: the specs of `Sprintf`, `Errorf` and `Printf` for
arguments that are all `nil` or `ArgWf` (`fmt.ArgsWf`), the statements they had before the
model called the arguments' methods (2026-11), for the callers that pass no other argument.
-/
module

public import Perennial.Proof.fmt.Link
public import Perennial.Proof.fmt.BytesResults

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `fmt.Sprintf` of arguments that are all `nil` or `ArgWf`. -/
theorem fmt.wp_Sprintf_argsWf :
    ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
    fmt.ArgsWf xs →
      {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs }}
        (App (App (Val (@! fmt.Sprintf)) (Val #format)) (Val #args_sl))
      {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ ⌜fmt.SprintfOut format xs s⌝ }} := by
  intro format args_sl xs dq Hxs
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  iapply (fmt.wp_Sprintf format args_sl xs dq) $$ [Hsl] HΦ
  iframe
  isplitr
  · iexact Hpkg
  iapply (fmt.argsOk_of_argsWf Hxs)

/-- `fmt.Printf` of arguments that are all `nil` or `ArgWf`. -/
theorem fmt.wp_Printf_argsWf :
    ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
    fmt.ArgsWf xs →
      {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs }}
        (App (App (Val (@! fmt.Printf)) (Val #format)) (Val #args_sl))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err); args_sl ↦*{dq} xs }} := by
  intro format args_sl xs dq Hxs
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  iapply (fmt.wp_Printf format args_sl xs dq) $$ [Hsl] HΦ
  iframe
  isplitr
  · iexact Hpkg
  iapply (fmt.argsOk_of_argsWf Hxs)

/-- `fmt.Errorf` of arguments that are all `nil` or `ArgWf`: a non-nil error whose `Error()`
returns some string (the arguments' slice is not given back). -/
theorem fmt.wp_Errorf_argsWf :
    ∀ (format : GoString) (args_sl : GoSlice) (args : List GoAny),
    fmt.ArgsWf args →
      {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
        (App (App (Val (@! fmt.Errorf)) (Val #format)) (Val #args_sl))
      {{ (err : GoInterfaceOk), RET #(interface.ok err);
          □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
            WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }} }} := by
  intro format args_sl args Hxs
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  iapply (fmt.wp_Errorf format args_sl args (DFrac.own 1)) $$ [Hsl]
  · iframe
    isplitr
    · iexact Hpkg
    iapply (fmt.argsOk_of_argsWf Hxs)
  inext
  iintro %err ⟨-, %s, -, Herr⟩
  iunfold fmt.errorfErr at Herr
  icases Herr with ⟨-, #HE, -⟩
  iapply HΦ
  imodintro
  iintro %Ψ HΨ
  iapply HE
  inext
  iapply HΨ

end results

end Perennial
