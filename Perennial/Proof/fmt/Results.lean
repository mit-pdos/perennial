/-
Results of `fmt` derived from the linked ones: `Fprintf` with the contents of its `[]byte` and
`[]string` arguments lent (`fmt.wp_Fprintf_bytes`); `Sprintf` without method arguments
(`fmt.wp_Sprintf_render`) and of `%016x-%016x.wal` (`fmt.wp_Sprintf_walName`); the specs of
`Errorf` and `Printf` (which format with the Go model's printer, `goose/model/overlay/fmt`) for
arguments that are all `nil` or `ArgWf` (`fmt.ArgsWf`), for the callers that pass no other argument.
-/
module

public import Perennial.Proof.fmt.PureArgs
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

/-- `fmt.Fprintf(w, format, args...)` with the contents of the `[]byte` and `[]string` arguments `B`
names lent: as `fmt.Fprintf.spec`, the formatted `s` with `SprintfOutB B format args s`; the lent
contents come back. -/
theorem fmt.wp_Fprintf_bytes :
    ∀ (B : GoInterface → Option fmt.Lent) (dqb : DFrac) (w : GoInterface) (format : GoString)
      (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac) (P : IProp GF)
      (Q : GoString → w64 → GoInterface → IProp GF),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.bytesOwn dqb B xs ∗
        fmt.argsOkB B fmt.methodVerbs format xs ∗ P ∗
        ∃ ii, ⌜w = interface.ok ii⌝ ∗ fmt.writeSpec ii P Q }}
      (App (App (App (Val (@! fmt.Fprintf)) (Val #w)) (Val #format)) (Val #args_sl))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err); args_sl ↦*{dq} xs ∗
        fmt.bytesOwn dqb B xs ∗ ∃ s : GoString, ⌜fmt.SprintfOutB B format xs s⌝ ∗ Q s n err }} := by
  intro B dqb w format args_sl xs dq P Q
  wp_start as ⟨Hsl, Hown, Hok, HP, %ii, %Hw, HW⟩
  subst Hw
  wp_auto
  wp_apply fmt.wp_newPrinter as %p Hp
  unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA
  icases Hp with ⟨%hnn, %F, %wid, %prec, %x', Hb, Hrest⟩
  have hdo := fmt.wp_doPrintfB (internal.gomodel.wp_Choose (GF := GF) (hG := hG))
    (internal.gomodel.wp_ChooseUint64 (GF := GF) (hG := hG)) fmt.buffer.wp_writeString
    (p.[fmt.pp, go!"buf"]) [] B dqb format args_sl xs dq false
  rw [fmt.modeVerbs_false] at hdo
  wp_apply hdo $$ [$Hb $Hsl $Hown $Hok] as %wsl %unk ⟨%s, Hb, Hsl, Hown, %Hs, -⟩
  try wp_auto
  unfold fmt.bufferOwn
  icases Hb with ⟨%sl, Hb, Hbs, Hcap⟩
  wp_auto
  wp_bind (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #sl))
  iunfold fmt.writeSpec at HW
  iapply HW $$ HP Hbs
  inext
  iintro %n %err Hbs HQ
  wp_auto
  wp_apply fmt.pp.wp_free p ([] ++ s) $$ [Hb Hbs Hcap Hrest]
  · iframe
    unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA fmt.bufferOwn
    isplitr
    · ipureintro; exact hnn
    iexists F, wid, prec, x'
    iframe
  try wp_auto
  iapply HΦ
  iframe
  ipureintro
  exact Hs

/-- `fmt.Sprintf` without `%q` and without method arguments returns `render ps args`
(`fmt.Out.eq_render`). -/
theorem fmt.wp_Sprintf_render :
    ∀ (format : GoString) (ps : List fmt.Piece) (args_sl : GoSlice) (xs : List GoInterface)
      (args : List fmt.Arg) (dq : DFrac),
    format = fmt.encode ps → fmt.Fits ps args → (∀ a ∈ args, a.NoMethod) → fmt.NoQuote ps →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗
        [∗list] x;a ∈ xs;args, fmt.isArg x a }}
      (App (App (Val (@! fmt.Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ ([∗list] x;a ∈ xs;args, fmt.isArg x a) ∗
        ⌜s = fmt.render ps args⌝ }} :=
  fmt.Sprintf_render_of fmt.wp_Sprintf

/-- `fmt.Sprintf` of arguments that call no method (`fmt.PureArgs`): some string with
`fmt.Out ps args s`, which is `fmt.render ps args` when the format has no `%q` (`fmt.NoQuote`). -/
theorem fmt.wp_Sprintf_pure :
    ∀ (format : GoString) (ps : List fmt.Piece) (args_sl : GoSlice) (xs : List GoInterface)
      (args : List fmt.Arg) (dq : DFrac),
    format = fmt.encode ps → fmt.Fits ps args → fmt.PureArgs xs args →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs }}
      (App (App (Val (@! fmt.Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗
        ⌜fmt.Out ps args s ∧ (fmt.NoQuote ps → s = fmt.render ps args)⌝ }} :=
  fmt.Sprintf_pure_of fmt.wp_Sprintf

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
