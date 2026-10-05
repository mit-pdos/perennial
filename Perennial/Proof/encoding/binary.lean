/-
Port of `new/proof/encoding/binary.v`: `encoding/binary` little-endian
`Uint64`/`PutUint64`/`Uint32`/`PutUint32`.
-/
import Perennial.Proof.sync
import Perennial.Proof.slices_proof.slices_init
import Perennial.Proof.math
import Perennial.Proof.io
import Perennial.Proof.errors
import Perennial.Code.encoding.binary
import Perennial.GeneratedProof.encoding.binary
import Perennial.Std.Word.LittleEndian

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
local macro "idx_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
      simp (disch := decide) only [sint_W64_lit]
      simp only [sint.nat, sint.Z, List.length_append, List.length_cons, List.length_nil] at *
      omega⟩)]))

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

/-- Rocq `is_init` (local). -/
abbrev isInit : IProp GF :=
  typed_pointsto (globalAddr LittleEndian) (zero_val littleEndian.t) DFrac.discard

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.encoding.binary :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.encoding.binary :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.encoding.binary get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.encoding.binary }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := interface.t) errOverflow go.error as _
  wp_apply wp_GlobalAlloc (V := littleEndian.t) LittleEndian littleEndian as Hlit
  ipersist Hlit
  wp_apply wp_GlobalAlloc (V := interface.t) errBufferTooSmall go.error as _
  wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H1⟩
  wp_apply slices.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply math.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply io.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H5⟩
  wp_apply errors.wp_New as %_ _
  wp_apply errors.wp_New as %_ _
  iframe Hown
  is_pkg_init_finish

theorem wp_littleEndian_Uint64 (le : littleEndian.t) (b : slice.t) (bs rem : List w8) (dq : DFrac)
    (Hlen_bs : bs.length = 8) :
    {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
      (App (Val (le @!! littleEndian @!! go!"Uint64")) (Val #b))
    {{ RET #(leToU64 bs); b ↦*{dq} (bs ++ rem) }} := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩ :
      ∃ w0 w1 w2 w3 w4 w5 w6 w7, bs = [w0, w1, w2, w3, w4, w5, w6, w7] := by
    match bs, Hlen_bs with
    | [w0, w1, w2, w3, w4, w5, w6, w7], _ => exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w7 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w0 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w1 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w2 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w3 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w4 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w5 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w6 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w7 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  rw [leToU64_8]
  iapply HΦ $$ Hb

theorem wp_littleEndian_PutUint64 (le : littleEndian.t) (b : slice.t) (space rem : List w8)
    (v : w64) (Hlen_space : space.length = 8) :
    {{ (b ↦* (space ++ rem) : IProp GF) }}
      (App (App (Val (le @!! littleEndian @!! go!"PutUint64")) (Val #b)) (Val #v))
    {{ RET #(); b ↦* (u64Le v ++ rem) }} := by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩ :
      ∃ w0 w1 w2 w3 w4 w5 w6 w7, space = [w0, w1, w2, w3, w4, w5, w6, w7] := by
    match space, Hlen_space with
    | [w0, w1, w2, w3, w4, w5, w6, w7], _ => exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  idx_if
  wp_apply wp_load_slice_index b _ _ _ w7 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  iapply HΦ
  rw [u64Le_8]
  simp only [Int.reduceToNat, List.cons_append, List.set_cons_succ, List.set_cons_zero]
  iexact Hb

theorem wp_littleEndian_PutUint32 (le : littleEndian.t) (b : slice.t) (space rem : List w8)
    (v : w32) (Hlen_space : space.length = 4) :
    {{ (b ↦* (space ++ rem) : IProp GF) }}
      (App (App (Val (le @!! littleEndian @!! go!"PutUint32")) (Val #b)) (Val #v))
    {{ RET #(); b ↦* (u32Le v ++ rem) }} := by
  obtain ⟨w0, w1, w2, w3, rfl⟩ : ∃ w0 w1 w2 w3, space = [w0, w1, w2, w3] := by
    match space, Hlen_space with
    | [w0, w1, w2, w3], _ => exact ⟨w0, w1, w2, w3, rfl⟩
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  idx_if
  wp_apply wp_load_slice_index b _ _ _ w3 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  iapply HΦ
  rw [u32Le_4]
  simp only [Int.reduceToNat, List.cons_append, List.set_cons_succ, List.set_cons_zero]
  iexact Hb

theorem wp_littleEndian_Uint32 (le : littleEndian.t) (b : slice.t) (bs rem : List w8) (dq : DFrac)
    (Hlen_bs : bs.length = 4) :
    {{ (b ↦*{dq} (bs ++ rem) : IProp GF) }}
      (App (Val (le @!! littleEndian @!! go!"Uint32")) (Val #b))
    {{ RET #(leToU32 bs); b ↦*{dq} (bs ++ rem) }} := by
  obtain ⟨w0, w1, w2, w3, rfl⟩ : ∃ w0 w1 w2 w3, bs = [w0, w1, w2, w3] := by
    match bs, Hlen_bs with
    | [w0, w1, w2, w3], _ => exact ⟨w0, w1, w2, w3, rfl⟩
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w3 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w0 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w1 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w2 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w3 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  rw [leToU32_4]
  iapply HΦ $$ Hb

theorem wp_LittleEndian_PutUint64 (b : slice.t) (space rem : List w8) (v : w64)
    (Hlen : space.length = 8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* (space ++ rem) }}
      (App (App (Val ((globalAddr LittleEndian) @!! go.type.PointerType littleEndian @!! go!"PutUint64"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* (u64Le v ++ rem) }} := by
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := isPkgInit_access (PROP := IProp GF) pkg_id.encoding.binary $$ Hpkg
  wp_auto
  wp_apply wp_littleEndian_PutUint64 _ b space rem v Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

theorem wp_LittleEndian_Uint64 (b : slice.t) (bs : List w8) (dq : DFrac) (rem : List w8)
    (Hlen : bs.length = 8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦*{dq} (bs ++ rem) }}
      (App (Val ((globalAddr LittleEndian) @!! go.type.PointerType littleEndian @!! go!"Uint64"))
        (Val #b))
    {{ RET #(leToU64 bs); b ↦*{dq} (bs ++ rem) }} := by
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := isPkgInit_access (PROP := IProp GF) pkg_id.encoding.binary $$ Hpkg
  wp_auto
  wp_apply wp_littleEndian_Uint64 _ b bs rem dq Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

theorem wp_LittleEndian_PutUint32 (b : slice.t) (space rem : List w8) (v : w32)
    (Hlen : space.length = 4) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦* (space ++ rem) }}
      (App (App (Val ((globalAddr LittleEndian) @!! go.type.PointerType littleEndian @!! go!"PutUint32"))
        (Val #b)) (Val #v))
    {{ RET #(); b ↦* (u32Le v ++ rem) }} := by
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := isPkgInit_access (PROP := IProp GF) pkg_id.encoding.binary $$ Hpkg
  wp_auto
  wp_apply wp_littleEndian_PutUint32 _ b space rem v Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

theorem wp_LittleEndian_Uint32 (b : slice.t) (bs : List w8) (dq : DFrac) (rem : List w8)
    (Hlen : bs.length = 4) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗ b ↦*{dq} (bs ++ rem) }}
      (App (Val ((globalAddr LittleEndian) @!! go.type.PointerType littleEndian @!! go!"Uint32"))
        (Val #b))
    {{ RET #(leToU32 bs); b ↦*{dq} (bs ++ rem) }} := by
  wp_start as Hb
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hle := isPkgInit_access (PROP := IProp GF) pkg_id.encoding.binary $$ Hpkg
  wp_auto
  wp_apply wp_littleEndian_Uint32 _ b bs rem dq Hlen $$ [$Hb] as Hb
  iapply HΦ $$ Hb

end wps

end encoding.binary

end Perennial
end
