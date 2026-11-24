/-
Shared definitions of the proofs of `internal/stringslite`: its `isPkgInit`, and what `Cut`
returns.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.stringslite
public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.stringslite

/-- What `Cut(s, sep)` returns: the text before and after the first occurrence of `sep` in `s`
and `true`, or `s`, `""` and `false` if `sep` does not occur in `s`. -/
def cut (s sep : GoString) : GoString × GoString × Bool :=
  let i := internal.bytealg.index s sep
  if 0 ≤ i then (s.take i.toNat, s.drop (i.toNat + sep.length), true) else (s, [], false)

/-- `Cut` found `sep`: `s` is `before ++ sep ++ after`, and `sep` occurs nowhere in `s` before
`before`'s end. -/
theorem cut_found (s sep before after : GoString) (h : cut s sep = (before, after, true)) :
    s = before ++ sep ++ after ∧ ∀ j < before.length, ¬ sep <+: s.drop j := by
  unfold cut at h
  rcases internal.bytealg.index_cases s sep with ⟨i, hi, hp, hmin⟩ | ⟨hi, -⟩
  · rw [hi] at h
    simp only [Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast, Prod.mk.injEq, and_true] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨u, hu⟩ := hp
    have hi' : i ≤ s.length := by
      have := (internal.bytealg.index_bounds s sep).2; rw [hi] at this; omega
    refine ⟨?_, fun j hj => hmin j (by simp at hj; omega)⟩
    have : s.drop (i + sep.length) = u := by
      rw [← List.drop_drop, ← hu, List.drop_left]
    rw [this, List.append_assoc, hu, List.take_append_drop]
  · rw [hi] at h; simp at h

/-- `Cut` did not find `sep`: `sep` occurs nowhere in `s`. -/
theorem cut_not_found (s sep before after : GoString) (h : cut s sep = (before, after, false)) :
    before = s ∧ after = [] ∧ ∀ j, ¬ sep <+: s.drop j := by
  unfold cut at h
  rcases internal.bytealg.index_cases s sep with ⟨i, hi, -, -⟩ | ⟨hi, hn⟩
  · rw [hi] at h; simp at h
  · rw [hi] at h
    simp only [Int.reduceNeg, Int.reduceLE, ↓reduceIte, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm, hn⟩

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.stringslite :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.stringslite :=
  build_get_is_pkg_init_wf

end wps

end internal.stringslite

end Perennial
