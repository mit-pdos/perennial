/-
The proof of `crypto/sha1.(*digest).checkSum`.
-/
module

public import Perennial.Spec.crypto.sha1.digest__checkSum
public import Perennial.Spec.crypto.internal.fips140only.Enforced
public import Perennial.Spec.crypto.sha1.digest__Write
public import Perennial.Spec.internal.byteorder.BEPutUint32
public import Perennial.Spec.internal.byteorder.BEPutUint64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha1.Assumptions]

/-- `BEPutUint32(a[k:], v)` on a `[20]byte` array `a`. -/
theorem crypto.sha1.put32_at
    (wp_BEPutUint32 : internal.byteorder.BEPutUint32.spec (GF := GF) (hG := hG))
    (a : Loc) (k : Nat) (hk : k + 4 ≤ 20) (vs : List w8) (hvs : vs.length = 20) (v : w32) :
    {{ (a ↦ (array.mk 20 vs : GoArray w8 20) : IProp GF) }}
      (App (App (Val (@! internal.byteorder.BEPutUint32))
        (Val #(slice.mk (arrayIndexRef w8 (sint.Z (W64 (k : Int))) a) (W64 20 - W64 (k : Int))
          (W64 20 - W64 (k : Int))))) (Val #v))
    {{ RET #(); a ↦ (array.mk 20 (vs.take k ++ (crypto.sha1.bytes32 v ++ vs.drop (k + 4))) :
        GoArray w8 20) }} := by
  iintro %Φ Ha HΦ
  have hkZ : sint.Z (W64 (k : Int)) = (k : Int) := by word
  have hsplit := array_split (V := w8) (GF := GF) (W64 (k : Int)) a (DFrac.own 1) 20
    (array.mk 20 vs) ⟨by omega, by omega⟩
  icases hsplit.1 $$ Ha with ⟨Ha1, Ha2⟩
  ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ Ha2
  have hkn : sint.nat (W64 (k : Int)) = k := by word
  have e20 : W64 20 - W64 (k : Int) = W64 (20 - sint.Z (W64 (k : Int))) := by word
  ihave Hs : (slice.mk (arrayIndexRef w8 (sint.Z (W64 (k : Int))) a) (W64 20 - W64 (k : Int))
      (W64 20 - W64 (k : Int)) ↦* ((vs.drop k).take 4 ++ (vs.drop k).drop 4)) $$ [Ha2]
  · rw [e20, List.take_append_drop]
    iapply crypto.sha1.slice_of_array_int _ _ ⟨by omega, by omega⟩ _ _ _ (by rw [← e20]; word)
    rw [hkn]
    iexact Ha2
  wp_apply (wp_BEPutUint32 _ ((vs.drop k).take 4) ((vs.drop k).drop 4) v (by simp; omega)) $$ [Hs]
    as Hs
  · iexact Hs
  rw [crypto.sha1.u32Le_rev] at *
  ihave Ha2 := crypto.sha1.array_of_slice_int _ (20 - sint.Z (W64 (k : Int))) ⟨by omega, by omega⟩
    _ _ _ Hnn2 $$ [Hs]
  · rw [← e20]; iexact Hs
  iapply HΦ
  have := crypto.sha1.array_join (GF := GF) a (W64 (k : Int)) 20
    ((array.mk 20 vs : GoArray w8 20).arr.take (sint.nat (W64 (k : Int))))
    (crypto.sha1.bytes32 v ++ (vs.drop k).drop 4) (DFrac.own 1) ⟨by omega, by omega⟩
    (by simp only [List.length_take]; omega)
  simp only [hkn, List.drop_drop] at this
  iapply this
  rw [hkn, List.drop_drop, show k + 4 = 4 + k by omega]
  dsimp only
  iframe

/-- `put32_at` at an integer offset. -/
theorem crypto.sha1.put32_at_int
    (wp_BEPutUint32 : internal.byteorder.BEPutUint32.spec (GF := GF) (hG := hG))
    (a : Loc) (k : Int) (hk0 : 0 ≤ k) (hk : k + 4 ≤ 20) (vs : List w8) (hvs : vs.length = 20) (v : w32) :
    {{ (a ↦ (array.mk 20 vs : GoArray w8 20) : IProp GF) }}
      (App (App (Val (@! internal.byteorder.BEPutUint32))
        (Val #(slice.mk (arrayIndexRef w8 (sint.Z (W64 k)) a) (W64 20 - W64 k)
          (W64 20 - W64 k)))) (Val #v))
    {{ RET #(); a ↦ (array.mk 20 (vs.take k.toNat ++ (crypto.sha1.bytes32 v ++ vs.drop (k.toNat + 4))) :
        GoArray w8 20) }} := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  simp only [Int.toNat_natCast]
  exact crypto.sha1.put32_at wp_BEPutUint32 a n (by omega) vs hvs v

theorem crypto.sha1.digest.checkSum.wp_proof
    (wp_Enforced : crypto.internal.fips140only.Enforced.spec (GF := GF) (hG := hG))
    (wp_Write : crypto.sha1.digest.Write.spec (GF := GF) (hG := hG))
    (wp_BEPutUint32 : internal.byteorder.BEPutUint32.spec (GF := GF) (hG := hG))
    (wp_BEPutUint64 : internal.byteorder.BEPutUint64.spec (GF := GF) (hG := hG)) :
    crypto.sha1.digest.checkSum.spec (GF := GF) (hG := hG) := by
  intro d v m Hoff Habs
  wp_start as Hd
  wp_auto
  wp_apply wp_Enforced as %b %Hb
  have hb : b = false := by
    cases b
    · rfl
    · exact absurd (Hb rfl) (crypto.fips140.godebugFips140_ne_only Hoff)
  subst hb
  wp_auto
  obtain ⟨Habs1, Hlen⟩ := Habs
  rw [Hlen]
  have hz72 : (_root_.Perennial.zero_val (GoArray w8 72)) = array.mk 72 (List.replicate 72 (W8 0)) := rfl
  rw [hz72]
  wp_apply crypto.sha1.wp_store_array_elem_int _ 72 (List.replicate 72 (W8 0)) (sint.Z (W64 0))
    ⟨by decide, by decide⟩ $$ [tmp]
    as tmp
  · iexact tmp
  have hmod := crypto.sha1.w64_mod64 m.length
  have hr64 : m.length % 64 < 64 := Nat.mod_lt _ (by decide)
  wp_join iprop(∃ tv : w64, "t" ∷ t_ptr ↦ tv ∗
      "%Ht" ∷ ⌜tv.toNat = (119 - m.length % 64) % 64 + 1⌝ ∗ "len" ∷ len_ptr ↦ W64 (m.length : Int))
    with [t len] as ⟨%tv, t, %Ht, len⟩
  · iexists _; iframe; ipureintro
    have : m.length % 64 < 56 := by simp only [uint.Z] at Hif; rw [hmod] at Hif; simp at Hif; omega
    rw [BitVec.toNat_sub, hmod]; simp; omega
  · iexists _; iframe; ipureintro
    have : 56 ≤ m.length % 64 := by simp only [uint.Z] at Hif; rw [hmod] at Hif; simp at Hif; omega
    rw [BitVec.toNat_sub, hmod]; simp; omega
  -- `padlen := tmp[:t+8]`
  have h0 : sint.Z (W64 0) = 0 := rfl
  have htN1 : 1 ≤ (119 - m.length % 64) % 64 + 1 := by omega
  have htN64 : (119 - m.length % 64) % 64 + 1 ≤ 64 := by omega
  generalize htN : (119 - m.length % 64) % 64 + 1 = tN at Ht htN1 htN64
  have htv8 : sint.Z (tv + W64 8) = ((tN + 8 : Nat) : Int) := by word
  have htvn : sint.nat (tv + W64 8) = tN + 8 := by word
  rw [if_pos ⟨by decide, by omega, by omega⟩]
  have hsplit := array_split (V := w8) (GF := GF) (tv + W64 8) tmp_ptr (DFrac.own 1) 72
    (array.mk 72 ((List.replicate 72 (W8 0)).set 0 (W8 128))) ⟨by omega, by omega⟩
  icases hsplit.1 $$ tmp with ⟨tmp1, -⟩
  ihave Hpad : (slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) tmp_ptr) (tv + W64 8 - W64 0) (W64 72 - W64 0) ↦*
      (W8 128 :: List.replicate (tN + 7) (W8 0))) $$ [tmp1]
  · rw [h0, go.arrayIndexRef_0, show tv + W64 8 - W64 0 = W64 (sint.Z (tv + W64 8)) by word]
    iapply crypto.sha1.slice_of_array_int _ _ ⟨by omega, by omega⟩ _ _ _
      (by rw [htv8, show sint.Z (W64 72 - W64 0) = 72 from rfl]; omega)
    rw [htvn]
    dsimp only
    rw [crypto.sha1.tmp_take tN (by omega)]
    iexact tmp1
  wp_auto
  -- `BEPutUint64(padlen[t:], len)`
  generalize hP : slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) tmp_ptr) (tv + W64 8 - W64 0)
    (W64 72 - W64 0) = P
  have hPlen : P.len = tv + W64 8 - W64 0 := by rw [← hP]
  have htvZ : sint.Z tv = (tN : Int) := by word
  have hPZ : sint.Z P.len = ((tN + 8 : Nat) : Int) := by rw [hPlen]; word
  rw [← hPlen, if_pos ⟨by omega, by omega,
    by rw [hPZ, show sint.Z (W64 72 - W64 0) = 72 from rfl]; omega⟩]
  have hps := ownSlice_split_all (V := w8) (GF := GF) tv P (DFrac.own 1)
    (W8 128 :: List.replicate (tN + 7) (W8 0)) ⟨by omega, by omega⟩
  icases hps.1 $$ Hpad with ⟨Hpa, Hpb⟩
  have htvn : sint.nat tv = tN := by word
  obtain ⟨hsp1, hsp2⟩ := crypto.sha1.tmp_split tN htN1
  rw [htvn, hsp1, hsp2] at hps ⊢
  wp_auto
  wp_apply (wp_BEPutUint64 _ (List.replicate 8 (W8 0)) [] _ (by simp)) $$ [Hpb] as Hpb
  · rw [List.append_nil]; iexact Hpb
  rw [List.append_nil, crypto.sha1.u64Le_rev, crypto.sha1.w64_shl3]
  -- `d.Write(padlen)`
  have hfirst : (W8 128 :: List.replicate (tN - 1) (W8 0)).length = tN := by simp; omega
  have hcomb := ownSlice_split_all (V := w8) (GF := GF) tv P (DFrac.own 1)
    ((W8 128 :: List.replicate (tN - 1) (W8 0)) ++ crypto.sha1.bytes64 (BitVec.ofNat 64 (m.length * 8)))
    ⟨by omega, by omega⟩
  rw [htvn, List.take_left' hfirst, List.drop_left' hfirst] at hcomb
  ihave Hpad := hcomb.2 $$ [Hpa Hpb]
  · iframe
  try wp_auto
  wp_apply (wp_Write d v m P (DFrac.own 1) _ Hoff ⟨Habs1, Hlen⟩) $$ [Hd Hpad] as ⟨%v', Hd, %Hv', Hpad⟩
  · iframe
  -- the padded message is whole blocks: `nx == 0`
  have htN' : tN - 1 = (119 - m.length % 64) % 64 := by omega
  have hpg := crypto.sha1.pad_go m
  rw [List.cons_append] at hpg
  rw [htN'] at Hv'
  simp only [List.cons_append] at Hv'
  rw [hpg] at Hv'
  obtain ⟨⟨Hh', Hnx', -⟩, -⟩ := Hv'
  have hpl : (crypto.sha1.pad m).length % 64 = 0 := by
    simp [crypto.sha1.pad, crypto.sha1.bytes64]; omega
  have hnx0 : v'.nx' = W64 0 := by rw [hpl] at Hnx'; word
  rw [hnx0]
  wp_auto
  -- the digest: the five state words, big-endian
  obtain ⟨hv', xv', nxv', lenv'⟩ := v'
  simp only at Hh' hnx0
  subst Hh'
  generalize hg : crypto.sha1.compressAll crypto.sha1.init (crypto.sha1.pad m) = g
  obtain ⟨g0, g1, g2, g3, g4⟩ := g
  ihave %Hdnn := typedPointsto_not_null _ _ _ $$ Hd
  iStructNamed Hd
  simp only [crypto.sha1.stArr]
  rw [show (_root_.Perennial.zero_val (GoArray w8 20)) = array.mk 20 (List.replicate 20 (W8 0)) from rfl]
  wp_apply crypto.sha1.wp_load_array_elem_int _ 5 [g0, g1, g2, g3, g4] (sint.Z (W64 0)) g0
    (by decide) (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ [h] as h
  · iexact h
  wp_apply (crypto.sha1.put32_at_int wp_BEPutUint32 digest_ptr 0 (by decide) (by decide)
    (List.replicate 20 (W8 0)) (by simp [crypto.sha1.bytes32]) g0) $$ [digest] as digest
  · iexact digest
  rw [show (List.replicate 20 (W8 0)).take ((0 : Int).toNat) ++ (crypto.sha1.bytes32 g0 ++
      (List.replicate 20 (W8 0)).drop ((0 : Int).toNat + 4)) = crypto.sha1.bytes32 g0 ++ (List.replicate 16 (W8 0)) by
    simp [crypto.sha1.bytes32]]
  wp_apply crypto.sha1.wp_load_array_elem_int _ 5 [g0, g1, g2, g3, g4] (sint.Z (W64 1)) g1
    (by decide) (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ [h] as h
  · iexact h
  wp_apply (crypto.sha1.put32_at_int wp_BEPutUint32 digest_ptr 4 (by decide) (by decide)
    (crypto.sha1.bytes32 g0 ++ (List.replicate 16 (W8 0))) (by simp [crypto.sha1.bytes32]) g1) $$ [digest] as digest
  · iexact digest
  rw [show (crypto.sha1.bytes32 g0 ++ (List.replicate 16 (W8 0))).take ((4 : Int).toNat) ++ (crypto.sha1.bytes32 g1 ++
      (crypto.sha1.bytes32 g0 ++ (List.replicate 16 (W8 0))).drop ((4 : Int).toNat + 4)) = crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (List.replicate 12 (W8 0))) by
    simp [crypto.sha1.bytes32]]
  wp_apply crypto.sha1.wp_load_array_elem_int _ 5 [g0, g1, g2, g3, g4] (sint.Z (W64 2)) g2
    (by decide) (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ [h] as h
  · iexact h
  wp_apply (crypto.sha1.put32_at_int wp_BEPutUint32 digest_ptr 8 (by decide) (by decide)
    (crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (List.replicate 12 (W8 0)))) (by simp [crypto.sha1.bytes32]) g2) $$ [digest] as digest
  · iexact digest
  rw [show (crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (List.replicate 12 (W8 0)))).take ((8 : Int).toNat) ++ (crypto.sha1.bytes32 g2 ++
      (crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (List.replicate 12 (W8 0)))).drop ((8 : Int).toNat + 4)) = crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (crypto.sha1.bytes32 g2 ++ (List.replicate 8 (W8 0)))) by
    simp [crypto.sha1.bytes32]]
  wp_apply crypto.sha1.wp_load_array_elem_int _ 5 [g0, g1, g2, g3, g4] (sint.Z (W64 3)) g3
    (by decide) (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ [h] as h
  · iexact h
  wp_apply (crypto.sha1.put32_at_int wp_BEPutUint32 digest_ptr 12 (by decide) (by decide)
    (crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (crypto.sha1.bytes32 g2 ++ (List.replicate 8 (W8 0))))) (by simp [crypto.sha1.bytes32]) g3) $$ [digest] as digest
  · iexact digest
  rw [show (crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (crypto.sha1.bytes32 g2 ++ (List.replicate 8 (W8 0))))).take ((12 : Int).toNat) ++ (crypto.sha1.bytes32 g3 ++
      (crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (crypto.sha1.bytes32 g2 ++ (List.replicate 8 (W8 0))))).drop ((12 : Int).toNat + 4)) = crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (crypto.sha1.bytes32 g2 ++ (crypto.sha1.bytes32 g3 ++ (List.replicate 4 (W8 0))))) by
    simp [crypto.sha1.bytes32]]
  wp_apply crypto.sha1.wp_load_array_elem_int _ 5 [g0, g1, g2, g3, g4] (sint.Z (W64 4)) g4
    (by decide) (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ [h] as h
  · iexact h
  wp_apply (crypto.sha1.put32_at_int wp_BEPutUint32 digest_ptr 16 (by decide) (by decide)
    (crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (crypto.sha1.bytes32 g2 ++ (crypto.sha1.bytes32 g3 ++ (List.replicate 4 (W8 0)))))) (by simp [crypto.sha1.bytes32]) g4) $$ [digest] as digest
  · iexact digest
  have e : (List.take 16 (crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++ (crypto.sha1.bytes32 g2 ++
      (crypto.sha1.bytes32 g3 ++ List.replicate 4 (W8 0))))) ++
      (crypto.sha1.bytes32 g4 ++ List.drop (16 + 4) (crypto.sha1.bytes32 g0 ++ (crypto.sha1.bytes32 g1 ++
        (crypto.sha1.bytes32 g2 ++ (crypto.sha1.bytes32 g3 ++ List.replicate 4 (W8 0))))))) =
      crypto.sha1.sha1 m := by
    rw [crypto.sha1.sha1_eq m, hg]
    simp [crypto.sha1.bytes32]
  rw [e]
  iapply HΦ
  iexists ⟨array.mk 5 [g0, g1, g2, g3, g4], xv', nxv', lenv'⟩
  iapply typedPointsto_combine _ _ _ Hdnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe
