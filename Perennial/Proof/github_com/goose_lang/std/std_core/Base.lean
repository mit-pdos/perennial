/-
Shared definitions of the proofs of `github.com/goose-lang/std/std_core` (overflow checks,
`Shuffle`, `Permutation`): its `isPkgInit` and arithmetic lemmas used by the proofs of
`Shuffle` and `Permutation`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.github_com.goose_lang.std.std_core
public import Perennial.GeneratedProof.github_com.goose_lang.std.std_core
public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.goose_lang.std.std_core

theorem umod_succ_bound (x i : w64) (hi : 0 ≤ sint.Z i) :
    0 ≤ sint.Z (x % (i + W64 1)) ∧ sint.Z (x % (i + W64 1)) ≤ sint.Z i := by
  have h0 : (i + W64 1).toNat ≠ 0 := by word
  have h2 : (x % (i + W64 1)).toNat < (i + W64 1).toNat := by
    rw [BitVec.toNat_umod]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero h0)
  constructor <;> word

theorem sint_eq_uint (x : w64) (h : 0 ≤ sint.Z x) : sint.Z x = uint.Z x := by word

theorem sint_succ_of_lt (i n : w64) (Hif : uint.Z i < uint.Z n) (Hi : 0 ≤ sint.Z i)
    (Hn : 0 ≤ sint.Z n) : sint.Z (i + W64 1) = sint.Z i + 1 := by word

theorem W64_sint (x : w64) : W64 (sint.Z x) = x := by simp [W64, sint.Z]

theorem seqZ_plus_1 (n m : Int) (h : 0 ≤ m) : seqZ n (m + 1) = seqZ n m ++ [n + m] := by
  unfold seqZ
  rw [show (m + 1).toNat = m.toNat + 1 by omega, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  congr 2
  omega

theorem perm_step (k m : Nat) (h : k < m) :
    (((seqZ 0 k).map (fun z => W64 z)) ++ List.replicate (m - k) (W64 0)).set k (W64 k) =
      ((seqZ 0 (k + 1)).map (fun z => W64 z)) ++ List.replicate (m - (k + 1)) (W64 0) := by
  rw [show m - k = (m - (k + 1)) + 1 by omega, List.replicate_succ]
  rw [list_set_middle _ _ _ _ _ (by simp [length_seqZ])]
  rw [seqZ_plus_1 _ _ (by omega)]
  simp

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.goose_lang.std.std_core :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.goose_lang.std.std_core :=
  build_get_is_pkg_init_wf

end wps

end github_com.goose_lang.std.std_core

end Perennial
end
