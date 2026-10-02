/-
Small additions to iris-lean's `gen_heap` used by the FFI layers.
-/
import Iris.BI.Lib.GenHeap

namespace Perennial

open Iris Iris.BI Iris.Std ProofMode

section
variable {GF : BundledGFunctors} {L V : Type _} {H : Type _ → Type _} [Std.LawfulFiniteMap H L]

/-- `gen_heap_valid` in its Rocq form: a wand to a pure fact, without an update
modality (so the proof mode keeps both hypotheses). -/
theorem genHeap_lookup [G : genHeapGS L V GF H] {σ : H V} {l : L} {dq : DFrac} {v : V} :
    ⊢@{IProp GF} genHeapInterp (G := G) σ -∗ pointsTo (G := G) l dq v -∗
      ⌜PartialMap.get? σ l = some v⌝ := by
  unfold genHeapInterp pointsTo
  iintro ⟨%m, -, Hσ, -⟩ Hl
  iapply ghost_map_lookup $$ Hσ Hl

/-- `genHeap_alloc` with the `genHeapGS` instance as a named argument. -/
theorem genHeap_alloc' [DecidableEq L] [G : genHeapGS L V GF H] {σ : H V} {l : L} {v : V}
    (Hσl : PartialMap.get? σ l = none) :
    genHeapInterp (G := G) σ ⊢ |==> (genHeapInterp (G := G) (PartialMap.insert σ l v) ∗
      pointsTo (G := G) l (.own 1) v ∗ metaToken (G := G) l ⊤) :=
  genHeap_alloc Hσl

/-- `genHeap_update` with the `genHeapGS` instance as a named argument. -/
theorem genHeap_update' [DecidableEq L] [G : genHeapGS L V GF H] {σ : H V} {l : L}
    {v₁ v₂ : V} :
    genHeapInterp (G := G) σ ∗ pointsTo (G := G) l (.own 1) v₁ ==∗
      genHeapInterp (G := G) (PartialMap.insert σ l v₂) ∗ pointsTo (G := G) l (.own 1) v₂ :=
  genHeap_update

end

end Perennial
