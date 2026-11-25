/-
Shared definitions of the proofs of the Go `math/rand` package: its `isPkgInit` (`isInit`, the
invariant of the global generator `globalRandGenerator` and the seeding table `rngCooked`), the
predicate of a generator over the runtime's source (`isRuntimeRand`) and the state of a local
source (`ownRngSource`).

Translated are the top-level functions that draw integers (`Int63`, `Int31`, `Int63n`, `Int31n`,
`Intn`), with the `Rand` methods they call, and a local generator `New(NewSource(seed))`. The
top-level functions draw from the global generator, which `globalRand` (a trusted model,
`TrustedCode/math/rand.lean`) creates on the first call: a `Rand` over the runtime's source, whose
`Int63` masks `runtime_rand()` (an arbitrary `uint64`, also a trusted model) to 63 bits.
`NewSource` returns an `*rngSource` (`rng.go`, the additive lagged Fibonacci generator, seeded from
`rngCooked`), `New` a `Rand` over any source. The specs say only that a result is in its range (the
distribution is not modelled), and of an `rngSource` only that its indices stay in range.
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Code.math.rand
public import Perennial.GeneratedProof.math.rand

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math.rand

/-- A word masked by a non-negative one is between zero and the mask (`runtimeSource.Int63`'s
`& rngMask`, `Int63n`'s and `Int31n`'s `& (n - 1)`). -/
theorem and_toInt_bounds {w : Nat} (x m : BitVec w) (hm : 0 ≤ m.toInt) :
    0 ≤ (x &&& m).toInt ∧ (x &&& m).toInt ≤ m.toInt := by
  have hle : (x &&& m).toNat ≤ m.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_right
  rw [BitVec.toInt_eq_toNat_cond] at hm
  rw [BitVec.toInt_eq_toNat_cond (x &&& m), BitVec.toInt_eq_toNat_cond m]
  split at hm <;> split <;> (try split) <;> omega

/-- `int32(x >> 32)` of a non-negative `int64` is non-negative (`Rand.Int31`). -/
theorem int31_nonneg_of_int63 (x : w64) (hx : 0 ≤ sint.Z x) :
    0 ≤ sint.Z (W32 (sint.Z (BitVec.sshiftRight' x (W64 32)))) := by
  have h1 : sint.Z (BitVec.sshiftRight' x (W64 32)) = sint.Z x / 2 ^ 32 := by
    simp only [sint.Z, BitVec.sshiftRight', BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    rfl
  have h2 := BitVec.toInt_lt (x := x)
  word

/-- The remainder of a non-negative word by a positive one is in `[0, n)` (`Int63n`, `Int31n`). -/
theorem srem_bounds {w : Nat} (y n : BitVec w) (hy : 0 ≤ y.toInt) (hn : 0 < n.toInt) :
    0 ≤ (y.srem n).toInt ∧ (y.srem n).toInt < n.toInt := by
  rw [BitVec.toInt_srem, Int.tmod_eq_emod_of_nonneg hy]
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ hn⟩

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The names in the trusted model of `globalRand` (`TrustedCode/math/rand.lean`, which comes before
the generated code and names its types and global by their strings). -/
theorem randTy_eq : randTy = Rand.ty := by unfold randTy Rand.ty; rfl
theorem runtimeSourceTy_eq : runtimeSourceTy = runtimeSource.ty := by
  unfold runtimeSourceTy runtimeSource.ty; rfl
theorem globalRandGeneratorTy_eq : globalRandGeneratorTy = sync.atomic.Pointer.ty Rand.ty := by
  unfold globalRandGeneratorTy; rw [randTy_eq]
theorem globalRandGenerator_name_eq :
    go!"math/rand.globalRandGenerator" = globalRandGenerator := by
  unfold globalRandGenerator; rfl

/-- An interface value holding a `*runtimeSource` (as `Rand`'s `src` and `s64` do in the global
generator). -/
def isRuntimeSource (i : GoInterface) : Prop :=
  ∃ p : Loc, i = interface.mkOk (go.PointerType runtimeSource.ty) #p

/-- `r` is a `Rand` over the runtime's source: both its sources are `*runtimeSource`s, and it is
never written (the methods that write it, `Seed` and `Read`, are not translated). -/
def isRuntimeRand (r : Loc) : IProp GF :=
  iprop(∃ v : Rand, r ↦□ v ∗ ⌜isRuntimeSource v.src' ∧ isRuntimeSource v.s64'⌝)

instance isRuntimeRand_persistent (r : Loc) : Persistent (isRuntimeRand (GF := GF) r) := by
  unfold isRuntimeRand; infer_instance
instance isRuntimeRand_timeless (r : Loc) : Timeless (isRuntimeRand (GF := GF) r) := by
  unfold isRuntimeRand; infer_instance

/-- The invariant's namespace. -/
abbrev globalRandN : Namespace := nroot.@"math_rand_globalRand"

/-- The state of `globalRandGenerator`: `nil` with the one-shot ghost variable `γ` pending, or a
generator over the runtime's source with `γ` shot (a persistent witness that the generator is
set, so that a `Load` after a failed `CompareAndSwap` sees it). -/
def globalState (γ : GName) (v : Loc) : IProp GF :=
  iprop((⌜v = null⌝ ∗ dghostVar γ (.own 1) ()) ∨ (isRuntimeRand v ∗ dghostVar γ .discard ()))

/-- What `math/rand`'s initialization gives: the invariant of `globalRandGenerator`, which holds
`nil` until the first `globalRand`, and a generator over the runtime's source from then on; and the
seeding table `rngCooked` (some array, read only: nothing writes it after initialization; its values
are not described, since no spec says anything about the numbers drawn). -/
def isInit : IProp GF :=
  iprop((∃ γ : GName, inv globalRandN iprop(∃ v : Loc,
    sync.atomic.ownPointer (T' := Rand) (globalAddr globalRandGenerator) (DFrac.own 1) v ∗
    globalState γ v)) ∗
    ∃ a : GoArray w64 607, typedPointsto (globalAddr rngCooked) a DFrac.discard)

instance isInit_persistent : Persistent (isInit (GF := GF)) := by
  unfold isInit; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.math.rand :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.rand :=
  build_get_is_pkg_init_wf

instance globalState_timeless (γ : GName) (v : Loc) :
    Timeless (globalState (GF := GF) γ v) := by
  unfold globalState; infer_instance

/-- The indices of an `rngSource` are in range (`[0, rngLen)`) and its array has `rngLen`
elements: what `Uint64` needs to index `vec` (nothing about the values in `vec`). -/
def rngSourceOk (v : rngSource) : Prop :=
  0 ≤ sint.Z v.tap' ∧ sint.Z v.tap' < 607 ∧ 0 ≤ sint.Z v.feed' ∧ sint.Z v.feed' < 607 ∧
    v.vec'.arr.length = 607

/-- `p` points to an `rngSource` (the state of a generator from `NewSource`: `Seed`, `Int63`
and `Uint64` write it, so the points-to is exclusive) whose indices are in range. -/
def ownRngSource (p : Loc) : IProp GF :=
  iprop(∃ v : rngSource, p ↦ v ∗ ⌜rngSourceOk v⌝)

instance ownRngSource_timeless (p : Loc) : Timeless (ownRngSource (GF := GF) p) := by
  unfold ownRngSource; infer_instance

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.math.rand ⊢ isInit (GF := GF) :=
  isPkgInit_access (PROP := IProp GF) pkg_id.math.rand

end wps

end math.rand

end Perennial
