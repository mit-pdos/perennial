/-
`fmt.Sprintf` and `fmt.Fprintf` with the bytes of their `[]byte` arguments lent: the arguments `B`
names (`[]byte`s holding the bytes `B` gives them, `fmt.bytesOwn`) are admitted under any directive
(`fmt.argsOkB`), Go reads their bytes, which come back, and the output is `fmt.SprintfOutB B`: `%s`,
`%v`, `%d`, `%x`, `%X` of such an argument, and `%q` of one of ASCII bytes, are formatted exactly.
With `B` always `none` these are `fmt.Sprintf.spec` and `fmt.Fprintf.spec` (`fmt.wp_doPrintf`).
-/
module

public import Perennial.Spec.fmt.Sprintf
public import Perennial.Spec.fmt.Fprintf
public import Perennial.Proof.fmt.DoPrintf

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

/-- `fmt.Sprintf(format, args...)` with the bytes of the `[]byte` arguments `B` names lent: a string
`s` with `SprintfOutB B format args s`; the arguments' slice and the lent bytes come back. -/
theorem fmt.wp_Sprintf_bytes :
    ∀ (B : GoInterface → Option GoString) (dqb : DFrac) (format : GoString) (args_sl : GoSlice)
      (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.bytesOwn dqb B xs ∗
        fmt.argsOkB B fmt.methodVerbs format xs }}
      (App (App (Val (@! fmt.Sprintf)) (Val #format)) (Val #args_sl))
    {{ (s : GoString), RET #s; args_sl ↦*{dq} xs ∗ fmt.bytesOwn dqb B xs ∗
        ⌜fmt.SprintfOutB B format xs s⌝ }} := by
  intro B dqb format args_sl xs dq
  wp_start as ⟨Hsl, Hown, Hok⟩
  wp_auto
  have hdo := fmt.wp_doPrintfB (GF := GF) B dqb format args_sl xs dq false
  rw [fmt.modeVerbs_false] at hdo
  wp_apply hdo $$ [$Hsl $Hown $Hok] as %s %wsl %unk ⟨Hsl, Hown, %Hs, -⟩
  iapply HΦ
  iframe
  ipureintro
  exact Hs

/-- `fmt.Fprintf(w, format, args...)` with the bytes of the `[]byte` arguments `B` names lent: as
`fmt.Fprintf.spec`, the formatted `s` with `SprintfOutB B format args s`; the lent bytes come back. -/
theorem fmt.wp_Fprintf_bytes :
    ∀ (B : GoInterface → Option GoString) (dqb : DFrac) (w : GoInterface) (format : GoString)
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
  try wp_auto
  have hdo := fmt.wp_doPrintfB (GF := GF) B dqb format args_sl xs dq false
  rw [fmt.modeVerbs_false] at hdo
  wp_apply hdo $$ [$Hsl $Hown $Hok] as %s %wsl %unk ⟨Hsl, Hown, %Hs, -⟩
  try wp_auto
  wp_apply (wp_printerBuf s) as %bsl ⟨Hb, %spare, Hspare⟩
  try wp_auto
  wp_bind (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #bsl))
  iunfold fmt.writeSpec at HW
  iapply HW $$ HP Hb
  inext
  iintro %n %err Hb HQ
  try wp_auto
  wp_apply (wp_retire bsl s spare) $$ [$Hb $Hspare]
  try wp_auto
  iapply HΦ
  iframe
  ipureintro
  exact Hs

end results

end Perennial
