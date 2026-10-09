/-
Package initialization of `crypto/rand` and `crypto/rand.Int`.
-/
module

public import Perennial.Proof.math.big
public import Perennial.Code.crypto.rand
public import Perennial.GeneratedProof.crypto.rand

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace crypto.rand

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What `crypto/rand`'s initialization gives: its package-level `Reader` (an
`io.Reader`). Its value is opaque: nothing is known about it beyond being the reader the
package installed, and `wp_Int` is stated for exactly that reader. -/
def isInitialized : IProp GF :=
  iprop(∃ rdr : GoInterface, "#Reader" ∷ (globalAddr Reader ↦□ rdr : IProp GF))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.crypto.rand :=
  define_is_pkg_init isInitialized
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.rand :=
  build_get_is_pkg_init_wf

theorem isInitialized_access :
    isPkgInit (PROP := IProp GF) pkg_id.crypto.rand ⊢ isInitialized :=
  isPkgInit_access (PROP := IProp GF) pkg_id.crypto.rand

variable [package_sem : crypto.rand.Assumptions]

/-- `crypto/rand.Int(rand.Reader, max)` returns a value in `[0, max)`, and no error, for
`0 < max < 2^63`. The bound on `max` is the range the model of `Int`
(`Perennial/TrustedCode/crypto/rand.lean`) covers; the reader is the package's own, which
never returns an error. -/
theorem wp_Int (rdr : GoInterface) (max : Loc) (mz : Int) (Hmz : 0 < mz ∧ mz < 2 ^ 63) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.crypto.rand ∗
       globalAddr Reader ↦□ rdr ∗ math.big.ownInt max mz }}
      (App (App (Val (@! Int')) (Val #rdr)) (Val #max))
    {{ (v : Loc) (z : Int), RET (PairV #v #interface.nil);
       math.big.ownInt max mz ∗ math.big.ownInt v z ∗ ⌜0 ≤ z ∧ z < mz⌝ }} := by
  wp_start as Hmax
  unfold math.big.ownInt
  icases Hmax with ⟨#HR, %x, %ws, Hp, Hws, %Hz, %Hnorm⟩
  -- `0 < mz < 2^63`: the sign is clear and the magnitude is one word, `mz`
  have Hneg : x.neg' = false := by
    cases h : x.neg'
    · rfl
    · simp only [h, ↓reduceIte] at Hz
      have := math.big.natValue_nonneg ws
      omega
  simp only [Hneg, Bool.false_eq_true, ↓reduceIte] at Hz
  have Hne : ws ≠ [] := by
    rintro rfl; simp only [math.big.natValue] at Hz; omega
  obtain ⟨m, rfl⟩ := math.big.natValue_one_word ws Hne Hnorm (by omega)
  have Hm : uint.Z m = mz := by simp only [math.big.natValue] at Hz; omega
  ihave %Hlen := ownSlice_len $$ Hws
  simp only [List.length_singleton] at Hlen
  wp_auto
  simp only [Hneg]
  wp_auto
  simp only [show x.abs'.len = W64 1 by word, decide_true, Bool.not_true]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  wp_apply wp_load_slice_index x.abs' (sint.Z (W64 0)) [m] (DFrac.own 1) m (by word) $$ [Hws]
    with Hws
  · iframe Hws; ipureintro; rfl
  have Hm0 : m ≠ W64 0 := by
    rintro rfl; revert Hm; simp only [show uint.Z (W64 0) = 0 from rfl]; omega
  simp only [decide_eq_false Hm0]
  wp_auto
  rw [decide_eq_false (show ¬ uint.Z (W64 (2 ^ 63)) ≤ uint.Z m by word)]
  wp_auto
  wp_apply wp_ArbitraryInt as %r _
  wp_apply math.big.wp_NewInt as %v Hv
  ispecialize HΦ $$ %v %(sint.Z (r % m))
  iapply HΦ
  isplitl [Hp Hws]
  · iexists x, [m]
    iframe
    ipureintro
    exact ⟨by simp only [Hneg, Bool.false_eq_true, ↓reduceIte, Hz], Hnorm⟩
  isplitl [Hv]
  · unfold math.big.ownInt
    icases Hv with ⟨%x', %ws', Hv, Hws', %Hv⟩
    iexists x', ws'
    iframe
    ipureintro
    exact Hv
  ipureintro
  have hm : 0 < m.toNat := by
    have : (0 : Int) < uint.Z m := by omega
    word
  have : (r % m).toNat < m.toNat := by rw [BitVec.toNat_umod]; exact Nat.mod_lt _ hm
  constructor <;> word

end wps

end crypto.rand

end Perennial
end
