/-
`fmt.Fprintf` (the trusted model's) with the contents of its `[]byte` and `[]string` arguments lent: the
arguments `B` names (`[]byte`s holding the bytes `B` gives them, `[]string`s holding the strings,
`fmt.bytesOwn`) are admitted under any directive (`fmt.argsOkB`), Go reads their contents, which come
back, and the output is `fmt.SprintfOutB B`: `%s`, `%v`, `%d`, `%x`, `%X` of a `[]byte`, and `%q` of
one of ASCII bytes, are formatted exactly, and `%s` and `%v` of a `[]string` (`fmt.stringsJoin`,
`fmt.SprintfOutB.strs_inv`).
With `B` always `none` this is `fmt.Fprintf.spec` (`fmt.wp_doPrintf`). (`Sprintf` is the real `fmt`'s:
`fmt.Sprintf.spec` lends `[]byte` arguments itself, `fmt.Arg.bytes`.)
-/
module

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

/-- **`%s` or `%v` of a lent `[]string` holding `ss` gives `stringsJoin ss`** (`[a b c]`), and
consumes the argument: the caller's way to read off the output of, e.g., `Fprintf(w, "%v", ss)`. -/
theorem fmt.SprintfOutB.strs_inv {B : GoInterface → Option fmt.Lent} {c : w8} {ii : GoInterfaceOk}
    {ss : List GoString} {f : GoString} {args : List GoInterface} {out : GoString}
    (hc : c = W8 115 ∨ c = W8 118) (hty : ii.ty = go.SliceType go.string)
    (hB : B (interface.ok ii) = some (.strings ss))
    (h : fmt.SprintfOutB B (W8 37 :: c :: f) (interface.ok ii :: args) out) :
    ∃ out', out = fmt.stringsJoin ss ++ out' ∧ fmt.SprintfOutB B f args out' := by
  have hns : ¬ fmt.IsStrArgType ii.ty := by
    rw [hty]
    rintro (h | ⟨-, h, -⟩)
    · simp [go.string] at h
    · rw [fmt.underlying_SliceType] at h; simp [go.string] at h
  have hni : ¬ fmt.IsIntArgType ii.ty := by
    rw [hty]
    rintro (h | ⟨h, -⟩)
    · simp [fmt.IsIntType, go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64,
        go.uint32, go.uint16, go.uint8] at h
    · rw [fmt.underlying_SliceType] at h
      simp [fmt.IsIntType, go.int, go.int64, go.int32, go.int16, go.int8, go.uint, go.uint64,
        go.uint32, go.uint16, go.uint8] at h
  have hnb : ii.ty ≠ go.SliceType go.byte := by
    rw [hty]; simp [go.byte, go.string, go.uint8]
  generalize hF : W8 37 :: c :: f = F at h
  generalize hA : interface.ok ii :: args = A at h
  cases h with
  | done => cases hF
  | extra => cases hF
  | byte _ _ _ _ hc' _ => exact absurd (List.cons.inj hF).1.symm hc'
  | percent =>
    have h2 := (List.cons.inj (List.cons.inj hF).2).1
    rcases hc with rfl | rfl <;> exact absurd h2 (by decide)
  | str ii' y f' args' out' hy _ | strV ii' y f' args' out' hy _ =>
    obtain ⟨hii, -⟩ := List.cons.inj hA
    cases hii
    exact absurd hy.1 hns
  | int _ _ _ ii' _ _ _ _ hz _ =>
    obtain ⟨hii, -⟩ := List.cons.inj hA
    cases hii
    exact absurd hz.isIntArgType hni
  | hex _ ii' _ _ _ _ _ =>
    have h2 := (List.cons.inj (List.cons.inj hF).2).1
    rcases hc with rfl | rfl <;> exact absurd h2 (by decide)
  | bytesS ii' _ _ _ _ hty' _ _ =>
    obtain ⟨hii, -⟩ := List.cons.inj hA
    cases hii
    exact absurd hty' hnb
  | bytesV _ ii' _ _ _ _ _ hty' _ _ =>
    obtain ⟨hii, -⟩ := List.cons.inj hA
    cases hii
    exact absurd hty' hnb
  | bytesX _ ii' _ _ _ _ hty' _ _ =>
    obtain ⟨hii, -⟩ := List.cons.inj hA
    cases hii
    exact absurd hty' hnb
  | bytesQ ii' _ _ _ _ hty' _ _ _ =>
    obtain ⟨hii, -⟩ := List.cons.inj hA
    cases hii
    exact absurd hty' hnb
  | strs c' ii' ss' f' args' out' _ _ hB' h' =>
    obtain ⟨-, hF2⟩ := List.cons.inj hF
    obtain ⟨-, rfl⟩ := List.cons.inj hF2
    obtain ⟨hii, rfl⟩ := List.cons.inj hA
    cases hii
    rw [hB] at hB'
    cases hB'
    exact ⟨out', rfl, h'⟩
  | other _ _ _ _ _ hnot =>
    obtain ⟨-, hf⟩ := List.cons.inj hF
    subst hf
    subst hA
    exact absurd ⟨ii, ss, rfl, hty, hB, hc⟩ hnot

/-- `Sprintf("%v", ss)` (or `"%s"`) of a lent `[]string` holding `ss` is `stringsJoin ss`. -/
theorem fmt.SprintfOutB.v_strings {B : GoInterface → Option fmt.Lent} {c : w8} {ii : GoInterfaceOk}
    {ss : List GoString} {out : GoString}
    (hc : c = W8 115 ∨ c = W8 118) (hty : ii.ty = go.SliceType go.string)
    (hB : B (interface.ok ii) = some (.strings ss))
    (h : fmt.SprintfOutB B [W8 37, c] [interface.ok ii] out) : out = fmt.stringsJoin ss := by
  obtain ⟨out', rfl, h'⟩ := fmt.SprintfOutB.strs_inv hc hty hB h
  rw [fmt.SprintfOutB.done_inv h', List.append_nil]

end results

end Perennial
