/-
Shared definitions of the `encoding/binary` proofs: the little-endian lemmas
(`leToU64_8`, `u64Le_8`, `u32Le_4`, `leToU32_4`, `sint_W64_lit`) and the bounds-check tactic
`idx_if` (scoped in `encoding.binary`), the package's `isPkgInit` (`LittleEndian` holds its
zero value), and `wp_load_struct_nofields`. The big-endian encoding of `v` is the
little-endian one reversed (`(u64Le v).reverse`), and big-endian decoding of `bs` is
little-endian decoding of `bs.reverse`.
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.slices.Base
public import Perennial.Proof.math.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.errors.Base
public import Perennial.Code.encoding.binary
public import Perennial.GeneratedProof.encoding.binary
public import Perennial.Std.Word.LittleEndian

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace encoding.binary

/-- `x ||| (b <<< k)` is `x + b * 2^k` when `x` fits in `k` bits. -/
theorem toNat_or_shl {n m : Nat} (x : BitVec n) (b : BitVec m) (k : Nat) (hx : x.toNat < 2 ^ k)
    (hk : k + m ≤ n) : (x ||| (b.setWidth n <<< k)).toNat = x.toNat + b.toNat * 2 ^ k := by
  have hb := b.isLt
  have hkm : b.toNat * 2 ^ k < 2 ^ n :=
    calc b.toNat * 2 ^ k < 2 ^ m * 2 ^ k := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos k)
      _ = 2 ^ (k + m) := by rw [← Nat.pow_add, Nat.add_comm]
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hk
  have hmn : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ n), Nat.mod_eq_of_lt hkm, Nat.or_comm,
    Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx, Nat.mul_comm, Nat.add_comm]

theorem leToU64_8 (w0 w1 w2 w3 w4 w5 w6 w7 : w8) :
    leToU64 [w0, w1, w2, w3, w4, w5, w6, w7] =
      W64 (uint.Z w0) ||| (W64 (uint.Z w1) <<< W64 8) ||| (W64 (uint.Z w2) <<< W64 16) |||
      (W64 (uint.Z w3) <<< W64 24) ||| (W64 (uint.Z w4) <<< W64 32) ||| (W64 (uint.Z w5) <<< W64 40) |||
      (W64 (uint.Z w6) <<< W64 48) ||| (W64 (uint.Z w7) <<< W64 56) := by
  simp only [leToU64, leToU64Def, LittleEndian.combine, W64, uint.Z, BitVec.ofInt_natCast,
    BitVec.ofNat_toNat, BitVec.shiftLeft_eq', BitVec.toNat_ofInt, Nat.reducePow, Int.cast_ofNat_Int,
    Int.reduceMod, Int.reduceToNat]
  apply BitVec.eq_of_toNat_eq
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt
  have := w4.isLt; have := w5.isLt; have := w6.isLt; have := w7.isLt
  have h0 : (w0.setWidth 64).toNat = w0.toNat := by simp; omega
  have h1 := toNat_or_shl (w0.setWidth 64) w1 8 (by omega) (by omega)
  have h2 := toNat_or_shl (w0.setWidth 64 ||| w1.setWidth 64 <<< 8) w2 16 (by omega) (by omega)
  have h3 := toNat_or_shl (w0.setWidth 64 ||| w1.setWidth 64 <<< 8 ||| w2.setWidth 64 <<< 16) w3 24
    (by omega) (by omega)
  have h4 := toNat_or_shl (w0.setWidth 64 ||| w1.setWidth 64 <<< 8 ||| w2.setWidth 64 <<< 16 |||
    w3.setWidth 64 <<< 24) w4 32 (by omega) (by omega)
  have h5 := toNat_or_shl (w0.setWidth 64 ||| w1.setWidth 64 <<< 8 ||| w2.setWidth 64 <<< 16 |||
    w3.setWidth 64 <<< 24 ||| w4.setWidth 64 <<< 32) w5 40 (by omega) (by omega)
  have h6 := toNat_or_shl (w0.setWidth 64 ||| w1.setWidth 64 <<< 8 ||| w2.setWidth 64 <<< 16 |||
    w3.setWidth 64 <<< 24 ||| w4.setWidth 64 <<< 32 ||| w5.setWidth 64 <<< 40) w6 48
    (by omega) (by omega)
  rw [toNat_or_shl _ w7 56 (by omega) (by omega), BitVec.toNat_ofNat]
  omega

theorem u64Le_8 (v : w64) :
    u64Le v = [W8 (uint.Z v), W8 (uint.Z (v >>> W64 8)), W8 (uint.Z (v >>> W64 16)),
      W8 (uint.Z (v >>> W64 24)), W8 (uint.Z (v >>> W64 32)), W8 (uint.Z (v >>> W64 40)),
      W8 (uint.Z (v >>> W64 48)), W8 (uint.Z (v >>> W64 56))] := by
  simp only [u64Le, u64LeDef, LittleEndian.split, W8, uint.Z, BitVec.ofInt_natCast, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | trivial | (apply BitVec.eq_of_toNat_eq; simp; omega)

theorem u32Le_4 (v : w32) :
    u32Le v = [W8 (uint.Z v), W8 (uint.Z (v >>> W32 8)), W8 (uint.Z (v >>> W32 16)),
      W8 (uint.Z (v >>> W32 24))] := by
  simp only [u32Le, u32LeDef, LittleEndian.split, W8, uint.Z, BitVec.ofInt_natCast, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | (apply BitVec.eq_of_toNat_eq; simp; omega)

theorem leToU32_4 (w0 w1 w2 w3 : w8) :
    leToU32 [w0, w1, w2, w3] =
      W32 (uint.Z w0) ||| (W32 (uint.Z w1) <<< W32 8) ||| (W32 (uint.Z w2) <<< W32 16) |||
      (W32 (uint.Z w3) <<< W32 24) := by
  simp only [leToU32, leToU32Def, LittleEndian.combine, W32, uint.Z, BitVec.ofInt_natCast,
    BitVec.ofNat_toNat, BitVec.shiftLeft_eq', BitVec.toNat_ofInt, Nat.reducePow, Int.cast_ofNat_Int,
    Int.reduceMod, Int.reduceToNat]
  apply BitVec.eq_of_toNat_eq
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt
  have h0 : (w0.setWidth 32).toNat = w0.toNat := by simp; omega
  have h1 := toNat_or_shl (w0.setWidth 32) w1 8 (by omega) (by omega)
  have h2 := toNat_or_shl (w0.setWidth 32 ||| w1.setWidth 32 <<< 8) w2 16 (by omega) (by omega)
  rw [toNat_or_shl _ w3 24 (by omega) (by omega), BitVec.toNat_ofNat]
  omega

theorem sint_W64_lit (z : Int) (h : 0 ≤ z ∧ z < 2 ^ 63) : sint.Z (W64 z) = z := by
  simp only [sint.Z, W64, BitVec.toInt_ofInt]
  apply Int.bmod_eq_of_le <;> omega

/-- Discharge the bounds check of a constant `IndexRef`. -/
scoped macro "idx_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
      simp (disch := decide) only [sint_W64_lit]
      simp only [sint.nat, sint.Z, List.length_append, List.length_cons, List.length_nil] at *
      omega⟩)]))

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

/-- The package-initialized state: `LittleEndian` holds its zero value. -/
abbrev isInit : IProp GF :=
  typedPointsto (globalAddr LittleEndian) (zero_val littleEndian) DFrac.discard

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.encoding.binary :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.encoding.binary :=
  build_get_is_pkg_init_wf

/-- Loading a struct with no fields reads no memory: it needs no points-to (the
`bigEndian` methods of the global `BigEndian` load it). -/
theorem wp_load_struct_nofields {V : Type} [ZeroVal V] {fds : List go.field_decl}
    [EqualsUnfold fds []] [go.TypeReprUnderlying (go.StructType fds) V]
    {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u go.StructType fds] (l : Loc) :
    {{ (emp : IProp GF) }} (App (Val (GoInstruction (GoLoad t))) (Val #l)) @ s; E
    {{ RET #(zero_val V); emp }} := by
  iintro %Φ _ HΦ
  have hpw : PureWp (hlc := hlc) (GF := GF) ((#l : val).isPanic = false)
      (App (Val (GoInstruction (GoLoad t))) (Val #l))
      (loadStructRaw fds #l []) := by
    have _tagged := @go.tagged_internal_inst
    infer_instance
  iapply (wp_pure_raw_step (Hwp := hpw) (by simp))
  inext
  rw [loadStructRaw_eq]
  simp only [List.foldl_nil]
  wp_pures
  iapply HΦ
  itrivial

end wps

end encoding.binary

end Perennial
