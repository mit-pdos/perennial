/-
Shared definitions of the proofs of `math/big`: its `isPkgInit`, the value of a magnitude
(`natValue`, `natNormalized`) and `ownInt`.

`ownInt p z` owns the `big.Int` at `p` and says it holds `z`. An `Int` is a sign
`neg` and a magnitude `abs`, a little-endian slice of 64-bit words. The
magnitude is normalized, as Go keeps it: no most significant zero word
(`natNormalized`), so a value has one representation (`crypto/rand.Int`'s model relies
on it: `0 < z < 2^63` is a one-word magnitude).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.math.big
public import Perennial.GeneratedProof.math.big
public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math.big

/-- The value of a little-endian list of 64-bit words. -/
def natValue : List w64 → Int
  | [] => 0
  | w :: ws => uint.Z w + 2 ^ 64 * natValue ws

theorem natValue_nonneg : ∀ ws : List w64, 0 ≤ natValue ws
  | [] => by unfold natValue; omega
  | w :: ws => by
    have := natValue_nonneg ws
    unfold natValue; have : 0 ≤ uint.Z w := by word
    omega

/-- A magnitude below `2^64` is its low word. -/
theorem natValue_small (ws : List w64) (h : natValue ws < 2 ^ 64) :
    natValue ws = uint.Z (ws.headD (W64 0)) := by
  cases ws with
  | nil => simp [natValue]; rfl
  | cons w ws =>
    have := natValue_nonneg ws
    have : 0 ≤ uint.Z w := by word
    simp only [natValue, List.headD] at h ⊢
    have : natValue ws = 0 := by omega
    omega

/-- No most significant zero word: how Go keeps a magnitude (`nat.norm`). -/
def natNormalized (ws : List w64) : Prop := ws.getLast? ≠ some (W64 0)

/-- A normalized magnitude with a word is positive. -/
theorem natValue_pos : ∀ ws : List w64, ws ≠ [] → natNormalized ws → 0 < natValue ws
  | [], h, _ => absurd rfl h
  | [w], _, hn => by
    simp only [natNormalized, List.getLast?_singleton, ne_eq, Option.some.injEq] at hn
    have : uint.Z w ≠ 0 := fun h => hn (by word)
    have : 0 ≤ uint.Z w := by word
    simp only [natValue]; omega
  | w :: w' :: ws, _, hn => by
    have ih := natValue_pos (w' :: ws) (List.cons_ne_nil _ _)
      (by simpa [natNormalized, List.getLast?_cons_cons] using hn)
    have : 0 ≤ uint.Z w := by word
    simp only [natValue] at ih ⊢; omega

/-- A normalized magnitude below `2^64` with a word is that one word. -/
theorem natValue_one_word (ws : List w64) (hne : ws ≠ []) (hn : natNormalized ws)
    (h : natValue ws < 2 ^ 64) : ∃ w, ws = [w] := by
  rcases ws with _ | ⟨w, _ | ⟨w', ws⟩⟩
  · exact absurd rfl hne
  · exact ⟨w, rfl⟩
  · have hpos := natValue_pos (w' :: ws) (List.cons_ne_nil _ _)
      (by simpa [natNormalized, List.getLast?_cons_cons] using hn)
    have : 0 ≤ uint.Z w := by word
    simp only [natValue] at h hpos; omega

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.math.big :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.big :=
  build_get_is_pkg_init_wf

variable [package_sem : math.big.Assumptions]

/-- `ownInt p z`: the `big.Int` at `p` holds `z`. Exclusive, since a `big.Int`
is mutable. -/
def ownInt (p : Loc) (z : Int) : IProp GF :=
  iprop(∃ (x : Int') (ws : List w64),
    p ↦ x ∗ x.abs' ↦* ws ∗
    ⌜(z = if x.neg' then - natValue ws else natValue ws) ∧ natNormalized ws⌝)

end wps

end math.big

end Perennial
