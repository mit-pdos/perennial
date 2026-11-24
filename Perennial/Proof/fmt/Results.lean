/-
Results of `fmt` derived from the linked ones: `Sprintf` without method arguments
(`fmt.wp_Sprintf_render`) and of `%016x-%016x.wal` (`fmt.wp_Sprintf_walName`); the specs of the
trusted models of `Errorf` and `Printf` for arguments that are all `nil` or `ArgWf`
(`fmt.ArgsWf`), the statements they had before the model called the arguments' methods (2026-11),
for the callers that pass no other argument.
-/
module

public import Perennial.Proof.fmt.Link
public import Perennial.Proof.fmt.BytesResults
public import Perennial.Proof.fmt.OutLemmas

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

/-- `fmt.Sprintf` without method arguments returns `render ps args` (`fmt.Out.eq_render`). -/
theorem fmt.wp_Sprintf_render :
    ∀ (format : GoString) (ps : List fmt.Piece) (args_sl : GoSlice) (xs : List GoInterface)
      (args : List fmt.Arg) (dq : DFrac),
    format = fmt.encode ps → fmt.Fits ps args → (∀ a ∈ args, a.NoMethod) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗
        [∗list] x;a ∈ xs;args, fmt.isArg x a }}
      (App (App (Val (@! fmt.Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ ([∗list] x;a ∈ xs;args, fmt.isArg x a) ∗
        ⌜s = fmt.render ps args⌝ }} :=
  fmt.Sprintf_render_of fmt.wp_Sprintf

/-- `fmt.Sprintf("%016x-%016x.wal", seq, index)` of two `uint64`s (etcd's WAL file names): each
zero-padded to 16 lowercase hexadecimal digits. -/
theorem fmt.wp_Sprintf_walName :
    ∀ (seq index : w64) (sl : GoSlice) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
        sl ↦*{dq} [interface.mkOk go.uint64 #seq, interface.mkOk go.uint64 #index] }}
      (App (App (Val (@! fmt.Sprintf)) (Val #(go!"%016x-%016x.wal"))) (Val #sl))
    {{ (r : GoString), RET #r;
        sl ↦*{dq} [interface.mkOk go.uint64 #seq, interface.mkOk go.uint64 #index] ∗
        ⌜r = fmt.hexPad 16 (uint.Z seq) ++ go!"-" ++ fmt.hexPad 16 (uint.Z index) ++ go!".wal"⌝ }} :=
  fmt.Sprintf_walName_of fmt.wp_Sprintf

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
