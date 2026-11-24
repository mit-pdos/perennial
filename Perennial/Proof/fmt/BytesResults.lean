/-
Lemmas on `fmt.SprintfOutB` (the output of `fmt.Fprintf` with the contents of its `[]byte` and
`[]string` arguments lent, `fmt.wp_Fprintf_bytes` in `Results.lean`): `%s` and `%v` of a lent
`[]string` give `fmt.stringsJoin` of its strings (`fmt.SprintfOutB.strs_inv`).
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
