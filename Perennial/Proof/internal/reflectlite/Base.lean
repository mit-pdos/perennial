/-
Shared definitions of the proofs of `internal/reflectlite` (the Go model,
`goose/model/overlay/internal/reflectlite`): its `isPkgInit` (no package variables).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.internal.reflectlite
public import Perennial.GeneratedProof.internal.reflectlite
public import Perennial.Proof.internal.abi.Base
public import Perennial.Proof.internal.gomodel.Base
public import Perennial.Proof.internal.reflectcore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.reflectlite

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.reflectlite :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.reflectlite :=
  build_get_is_pkg_init_wf

end init

/-- A kind is below 27. -/
theorem kindOf_lt {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (h : go.kindOf u = some k) : k < 27 := by
  unfold go.kindOf at h
  split at h <;> try (cases h; omega)
  simp only [List.find?] at h
  repeat (first | (split at h <;> try (cases h; omega)) | (simp at h; omega))
  all_goals simp_all

/-- `Kind(TypeKind(t))` (`int` to `abi.Kind`, a `uint8`) of a kind `k` is `W8 k`. -/
theorem kind_w8 {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (h : go.kindOf u = some k) : (W8 (sint.Z (W64 (k : Int))) : w8) = W8 (k : Int) := by
  have hlt := kindOf_lt h
  have hz : sint.Z (W64 (k : Int)) = k := by
    simp only [sint.Z, W64, BitVec.toInt_ofInt]
    rw [Int.bmod_def]
    split <;> omega
  rw [hz]

/-- A kind other than `Struct` is another `abi.Kind` than `Struct`'s. -/
theorem kind_ne_struct {u : go.GoType} [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {k : Nat}
    (h : go.kindOf u = some k) (hk : k ≠ 25) : (W8 (sint.Z (W64 (k : Int))) : w8) ≠ W8 25 := by
  rw [kind_w8 h]
  have key : ∀ k : Nat, k < 27 → k ≠ 25 → (W8 (k : Int) : w8) ≠ W8 25 := by decide
  exact key k (kindOf_lt h) hk

end internal.reflectlite

end Perennial
