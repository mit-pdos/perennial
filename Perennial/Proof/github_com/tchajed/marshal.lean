/-
Port of `new/proof/github_com/tchajed/marshal.v`: specs for the stateless
`github.com/tchajed/marshal` encoding helpers.
-/
import Perennial.Proof.github_com.goose_lang.std
import Perennial.Proof.github_com.goose_lang.primitive
import Perennial.Proof.encoding.binary
import Perennial.Code.github_com.tchajed.marshal
import Perennial.GeneratedProof.github_com.tchajed.marshal
import Perennial.Std.Word.LittleEndian

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace github_com.tchajed.marshal

/-! Some helper definitions for working with slices of primitive values. -/

def uint64_has_encoding (encoded : List w8) (x : w64) : Prop := encoded = u64_le x

def uint32_has_encoding (encoded : List w8) (x : w32) : Prop := encoded = u32_le x

def bool_has_encoding (encoded : List w8) (x : Bool) : Prop :=
  encoded = [if x then W8 1 else W8 0]

def string_has_encoding (encoded : List w8) (x : go_string) : Prop := encoded = x

def byte_has_encoding (encoded : List w8) (x : List w8) : Prop := encoded = x

def encodes {A : Type} (enc : List w8) (xs : List A) (has_encoding : List w8 → A → Prop) : Prop :=
  match xs with
  | [] => enc = []
  | x :: xs' => ∃ bs bs', xs = x :: xs' ∧ enc = bs ++ bs' ∧ has_encoding bs x ∧
      encodes bs' xs' has_encoding

theorem drop_succ {A : Type} (l : List A) (x : A) (l' : List A) (n : Nat)
    (_Helem : l[n]? = some x) (Hd : l.drop n = x :: l') : l.drop (n + 1) = l' := by
  rw [← List.drop_drop, Hd]; rfl

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.github_com.tchajed.marshal :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tchajed.marshal :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg_id.github_com.tchajed.marshal get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗
        is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply github_com.goose_lang.std.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H1⟩
  wp_apply encoding.binary.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H2⟩
  iframe Hown
  is_pkg_init_finish

theorem sint_lt_2_63 (x : w64) : sint.Z x < 2 ^ 63 := by word

theorem sint_of_uint_le (x : w64) (y : Int) (h : uint.Z x ≤ y) (hy : y < 2 ^ 63) :
    sint.Z x = uint.Z x := by word

theorem room8 (l c : w64) (hroom : uint.Z (W64 8) ≤ uint.Z c - uint.Z l)
    (hwf : 0 ≤ sint.Z l ∧ sint.Z l ≤ sint.Z c) :
    sint.Z (l + W64 8) = sint.Z l + 8 ∧ sint.Z (l + W64 8) ≤ sint.Z c := by
  constructor <;> word

theorem room4 (l c : w64) (hroom : uint.Z (W64 4) ≤ uint.Z c - uint.Z l)
    (hwf : 0 ≤ sint.Z l ∧ sint.Z l ≤ sint.Z c) :
    sint.Z (l + W64 4) = sint.Z l + 4 ∧ sint.Z (l + W64 4) ≤ sint.Z c := by
  constructor <;> word

theorem own_slice_split_app (k : w64) (s : slice.t) (dq : DFrac) (head tail : List w8)
    (hk : sint.nat k = head.length) (hk0 : 0 ≤ sint.Z k)
    (hlen : (head ++ tail).length = sint.nat s.len) (hs : 0 ≤ sint.Z s.len) :
    (s ↦*{dq} (head ++ tail) : IProp GF) ⊢
      slice.slice s w8 (W64 0) k ↦*{dq} head ∗ slice.slice s w8 k s.len ↦*{dq} tail := by
  have hb : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.len := by
    simp only [List.length_append, sint.nat, sint.Z] at hlen hk hk0 hs ⊢
    refine ⟨hk0, ?_, Int.le_refl _⟩; omega
  refine (own_slice_slice k s.len s dq _ hb).1.trans ?_
  have h1 : (head ++ tail).take (sint.nat k) = head := by rw [hk]; simp
  have h2 : subslice (sint.nat k) (sint.nat s.len) (head ++ tail) = tail := by
    simp only [subslice]; rw [← hlen, List.take_length, hk]; simp
  rw [h1, h2]
  iintro ⟨H1, H2, _⟩
  iframe

theorem wp_ReadInt (tail : List w8) (s : slice.t) (dq : DFrac) (x : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦*{dq} (u64_le x ++ tail) }}
      (App (Val (@! ReadInt)) (Val #s))
    {{ (s' : slice.t), RET (PairV #x #s'); s' ↦*{dq} tail }} := by
  wp_start as Hs
  ihave %Hlen := own_slice_len _ _ _ $$ Hs
  ihave %Hwf := own_slice_wf _ _ _ $$ Hs
  ihave #Hbin : is_pkg_init (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  wp_apply encoding.binary.wp_LittleEndian_Uint64 s (u64_le x) dq tail (u64_le_length x) $$ [$Hs]
    as Hs
  rw [u64_le_to_word]
  simp only [List.length_append, u64_le_length] at Hlen
  have h8 : sint.Z (W64 8) = 8 := by decide
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
    rw [h8]; simp only [sint.nat, sint.Z] at *; omega, Hwf.2⟩)]
  wp_auto
  iapply HΦ
  icases own_slice_split_app (W64 8) s dq (u64_le x) tail (by rw [u64_le_length]; decide)
    (by decide) (by simp [u64_le_length, Hlen]) Hwf.1 $$ Hs with ⟨_, Hs⟩
  iexact Hs

theorem wp_ReadInt32 (tail : List w8) (s : slice.t) (dq : DFrac) (x : w32) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦*{dq} (u32_le x ++ tail) }}
      (App (Val (@! ReadInt32)) (Val #s))
    {{ (s' : slice.t), RET (PairV #x #s'); s' ↦*{dq} tail }} := by
  wp_start as Hs
  ihave %Hlen := own_slice_len _ _ _ $$ Hs
  ihave %Hwf := own_slice_wf _ _ _ $$ Hs
  ihave #Hbin : is_pkg_init (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  wp_apply encoding.binary.wp_LittleEndian_Uint32 s (u32_le x) dq tail (u32_le_length x) $$ [$Hs]
    as Hs
  rw [u32_le_to_word]
  simp only [List.length_append, u32_le_length] at Hlen
  have h4 : sint.Z (W64 4) = 4 := by decide
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
    rw [h4]; simp only [sint.nat, sint.Z] at *; omega, Hwf.2⟩)]
  wp_auto
  iapply HΦ
  icases own_slice_split_app (W64 4) s dq (u32_le x) tail (by rw [u32_le_length]; decide)
    (by decide) (by simp [u32_le_length, Hlen]) Hwf.1 $$ Hs with ⟨_, Hs⟩
  iexact Hs

theorem wp_ReadBytes (s : slice.t) (dq : DFrac) (len : w64) (head tail : List w8)
    (Hlen : head.length = uint.nat len) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦*{dq} (head ++ tail) }}
      (App (App (Val (@! ReadBytes)) (Val #s)) (Val #len))
    {{ (b s' : slice.t), RET (PairV #b #s'); b ↦*{dq} head ∗ s' ↦*{dq} tail }} := by
  wp_start as Hs
  ihave %Hsz := own_slice_len _ _ _ $$ Hs
  ihave %Hwf := own_slice_wf _ _ _ $$ Hs
  simp only [List.length_append] at Hsz
  have hu : uint.Z len ≤ sint.Z s.len := by
    have := Hwf.1; simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega
  have he := sint_of_uint_le len _ hu (sint_lt_2_63 _)
  have hl : sint.Z len = uint.Z len ∧ 0 ≤ sint.Z len ∧ sint.Z len ≤ sint.Z s.len := by
    have := uint_Z_nonneg len
    refine ⟨he, ?_, ?_⟩ <;> omega
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, hl.2.1, by have := Hwf.2; omega⟩)]
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hl.2.1, hl.2.2, Hwf.2⟩)]
  wp_auto
  iapply HΦ
  icases own_slice_split_app len s dq head tail
    (by simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega) hl.2.1
    (by simp only [List.length_append]; omega) Hwf.1 $$ Hs with ⟨H1, H2⟩
  iframe

theorem wp_ReadLenPrefixedBytes (s : slice.t) (q : DFrac) (len : w64) (head tail : List w8)
    (Hlen : head.length = uint.nat len) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗
        s ↦*{q} (u64_le len ++ head ++ tail) }}
      (App (Val (@! ReadLenPrefixedBytes)) (Val #s))
    {{ (b s' : slice.t), RET (PairV #b #s'); b ↦*{q} head ∗ s' ↦*{q} tail }} := by
  wp_start as Hs
  wp_auto
  rw [List.append_assoc]
  wp_apply wp_ReadInt (head ++ tail) s q len $$ [$Hs] as %s1 Hs
  wp_apply wp_ReadBytes s1 q len head tail Hlen $$ [$Hs] as %b %s2 ⟨Hb, Hs⟩
  iapply HΦ
  iframe

theorem wp_ReadBytesCopy (s : slice.t) (q : DFrac) (len : w64) (head tail : List w8)
    (Hlen : head.length = uint.nat len) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦*{q} (head ++ tail) }}
      (App (App (Val (@! ReadBytesCopy)) (Val #s)) (Val #len))
    {{ (b s' : slice.t), RET (PairV #b #s'); b ↦*{DFrac.own 1} head ∗ s' ↦*{q} tail }} := by
  wp_start as Hs
  ihave %Hsz := own_slice_len _ _ _ $$ Hs
  ihave %Hwf := own_slice_wf _ _ _ $$ Hs
  simp only [List.length_append] at Hsz
  have hu : uint.Z len ≤ sint.Z s.len := by
    have := Hwf.1; simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega
  have he := sint_of_uint_le len _ hu (sint_lt_2_63 _)
  have hl : 0 ≤ sint.Z len ∧ sint.Z len ≤ sint.Z s.len := by
    have := uint_Z_nonneg len
    refine ⟨?_, ?_⟩ <;> omega
  wp_auto
  wp_apply wp_slice_make2 (V := w8) len $$ [] as %sl ⟨Hsl, Hcap⟩
  · ipureintro; exact hl.1
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, hl.1, by have := Hwf.2; omega⟩)]
  have hhd : sint.nat len = head.length := by simp only [sint.nat, uint.nat, sint.Z, uint.Z] at *; omega
  icases own_slice_split_app len s q head tail hhd hl.1
    (by simp only [List.length_append]; omega) Hwf.1 $$ Hs with ⟨Hhead, Htail⟩
  wp_auto
  wp_apply wp_slice_copy (V := w8) (t := go.byte) sl _ _ head q $$ [$Hsl $Hhead]
    as %n ⟨%Hn, Hsl, Hhead⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hl.1, hl.2, Hwf.2⟩)]
  wp_auto
  iapply HΦ
  iframe Htail
  rw [List.length_replicate, hhd, List.take_length, List.drop_eq_nil_of_le (by simp),
    List.append_nil]
  iexact Hsl

theorem wp_ReadBool (s : slice.t) (q : DFrac) (bit : w8) (tail : List w8) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦*{q} (bit :: tail) }}
      (App (Val (@! ReadBool)) (Val #s))
    {{ (b : Bool) (s' : slice.t), RET (PairV #b #s');
        ⌜b = decide (uint.Z bit ≠ 0)⌝ ∗ s' ↦*{q} tail }} := by
  wp_start as Hs
  ihave %Hsz := own_slice_len _ _ _ $$ Hs
  ihave %Hwf := own_slice_wf _ _ _ $$ Hs
  simp only [List.length_cons] at Hsz
  have h1 : sint.Z (W64 1) = 1 := by decide
  have hs1 : 1 ≤ sint.Z s.len := by simp only [sint.nat, sint.Z] at *; omega
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩)]
  wp_apply wp_load_slice_index s _ _ q bit (by decide) $$ [Hs] with Hs
  · iframe Hs; ipureintro; rfl
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [h1]; exact hs1, Hwf.2⟩)]
  wp_auto
  iapply HΦ
  rw [show bit :: tail = [bit] ++ tail from rfl]
  icases own_slice_split_app (W64 1) s q [bit] tail rfl (by decide)
    (by simp only [List.cons_append, List.nil_append, List.length_cons]; exact Hsz.1) Hwf.1 $$ Hs
    with ⟨_, Hs⟩
  iframe Hs
  ipureintro
  by_cases hb : bit = W8 0
  · subst hb; decide
  · have : uint.Z bit ≠ 0 := fun h => hb (by simp only [uint.Z] at h; exact BitVec.eq_of_toNat_eq (by simp; omega))
    simp only [hb, this, decide_false, Bool.not_false, ne_eq, not_false_eq_true, decide_true]

theorem wp_compute_new_cap (old_cap min_cap : w64) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal }}
      (App (App (Val (@! compute_new_cap)) (Val #old_cap)) (Val #min_cap))
    {{ (new_cap : w64), RET #new_cap; ⌜uint.Z min_cap ≤ uint.Z new_cap⌝ }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro; omega
  · iapply HΦ; ipureintro; simp only [uint.Z] at *; omega

theorem wp_reserve (s : slice.t) (extra : w64) (vs : List w8) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        own_slice_cap w8 s (DFrac.own 1) }}
      (App (App (Val (@! reserve)) (Val #s)) (Val #extra))
    {{ (s' : slice.t), RET #s';
        ⌜uint.Z extra ≤ uint.Z s'.cap - uint.Z s'.len⌝ ∗
        s' ↦* vs ∗ own_slice_cap w8 s' (DFrac.own 1) }} := by
  -- Rocq: Admitted. As stated this is not provable: if the new capacity computed
  -- by `compute_new_cap` is at least 2^63, `make3` panics.
  sorry -- Rocq: Admitted

theorem wp_WriteInt (s : slice.t) (x : w64) (vs : List w8) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        own_slice_cap w8 s (DFrac.own 1) }}
      (App (App (Val (@! WriteInt)) (Val #s)) (Val #x))
    {{ (s' : slice.t), RET #s'; s' ↦* (vs ++ u64_le x) ∗ own_slice_cap w8 s' (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hcap⟩
  ihave #Hbin : is_pkg_init (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_reserve s (W64 8) vs $$ [$Hs $Hcap] as %s2 ⟨%Hroom, Hs, Hcap⟩
  ihave %Hsz := own_slice_len _ _ _ $$ Hs
  ihave %Hcapwf := own_slice_cap_wf _ _ $$ Hcap
  have hr := room8 _ _ Hroom Hcapwf
  have h0 : sint.Z (W64 0) = 0 := rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by omega, hr.2⟩)]
  icases own_slice_slice_into_capacity (W64 0) (s2.len + W64 8) s2 vs $$ [Hs Hcap] with
    ⟨%vs_cap, -, Hb3, Hb3cap⟩
  · iframe; ipureintro; omega
  simp only [List.drop_zero, show sint.nat (W64 0) = 0 from rfl] at *
  generalize hB : slice.slice s2 w8 (W64 0) (s2.len + W64 8) = B
  ihave %HBwf := own_slice_cap_wf _ _ $$ Hb3cap
  ihave %Hb3len := own_slice_len _ _ _ $$ Hb3
  have hBlen : B.len = s2.len + W64 8 := by
    rw [← hB]; show s2.len + W64 8 - W64 0 = _; simp
  rw [hBlen, hr.1] at Hb3len
  rw [hBlen] at HBwf
  have hvc : vs_cap.length = 8 := by
    have h1 := hr.1; simp only [List.length_append, sint.nat, sint.Z] at *; omega
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hcapwf.1, by rw [hBlen]; omega, by rw [hBlen]; exact HBwf.2⟩)]
  icases own_slice_split_app s2.len B (DFrac.own 1) vs vs_cap Hsz.1.symm Hcapwf.1
    (by rw [hBlen]; simp only [List.length_append, sint.nat] at *; omega)
    (by rw [hBlen]; omega) $$ Hb3 with ⟨H0, Hput⟩
  rw [← List.append_nil vs_cap]
  wp_auto
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 _ vs_cap [] x hvc $$ [$Hput] as Hput
  iapply HΦ
  iframe Hb3cap
  iapply (own_slice_trivial_slice B _ _).2
  iapply own_slice_combine s2.len B (DFrac.own 1) vs (u64_le x) (W64 0) B.len
    ⟨by rw [Hsz.1]; simp only [sint.nat, show (W64 0).toInt = 0 from rfl]; omega, by decide, Hcapwf.1, by rw [hBlen]; omega⟩
    $$ H0
  rw [List.append_nil]
  iexact Hput

theorem wp_WriteInt32 (s : slice.t) (x : w32) (vs : List w8) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        own_slice_cap w8 s (DFrac.own 1) }}
      (App (App (Val (@! WriteInt32)) (Val #s)) (Val #x))
    {{ (s' : slice.t), RET #s'; s' ↦* (vs ++ u32_le x) ∗ own_slice_cap w8 s' (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hcap⟩
  ihave #Hbin : is_pkg_init (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_reserve s (W64 4) vs $$ [$Hs $Hcap] as %s2 ⟨%Hroom, Hs, Hcap⟩
  ihave %Hsz := own_slice_len _ _ _ $$ Hs
  ihave %Hcapwf := own_slice_cap_wf _ _ $$ Hcap
  have hr := room4 _ _ Hroom Hcapwf
  have h0 : sint.Z (W64 0) = 0 := rfl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by omega, hr.2⟩)]
  icases own_slice_slice_into_capacity (W64 0) (s2.len + W64 4) s2 vs $$ [Hs Hcap] with
    ⟨%vs_cap, -, Hb3, Hb3cap⟩
  · iframe; ipureintro; omega
  simp only [List.drop_zero, show sint.nat (W64 0) = 0 from rfl] at *
  generalize hB : slice.slice s2 w8 (W64 0) (s2.len + W64 4) = B
  ihave %HBwf := own_slice_cap_wf _ _ $$ Hb3cap
  ihave %Hb3len := own_slice_len _ _ _ $$ Hb3
  have hBlen : B.len = s2.len + W64 4 := by
    rw [← hB]; show s2.len + W64 4 - W64 0 = _; simp
  rw [hBlen, hr.1] at Hb3len
  rw [hBlen] at HBwf
  have hvc : vs_cap.length = 4 := by
    have h1 := hr.1; simp only [List.length_append, sint.nat, sint.Z] at *; omega
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hcapwf.1, by rw [hBlen]; omega, by rw [hBlen]; exact HBwf.2⟩)]
  icases own_slice_split_app s2.len B (DFrac.own 1) vs vs_cap Hsz.1.symm Hcapwf.1
    (by rw [hBlen]; simp only [List.length_append, sint.nat] at *; omega)
    (by rw [hBlen]; omega) $$ Hb3 with ⟨H0, Hput⟩
  rw [← List.append_nil vs_cap]
  wp_auto
  wp_apply encoding.binary.wp_LittleEndian_PutUint32 _ vs_cap [] x hvc $$ [$Hput] as Hput
  iapply HΦ
  iframe Hb3cap
  iapply (own_slice_trivial_slice B _ _).2
  iapply own_slice_combine s2.len B (DFrac.own 1) vs (u32_le x) (W64 0) B.len
    ⟨by rw [Hsz.1]; simp only [sint.nat, show (W64 0).toInt = 0 from rfl]; omega, by decide, Hcapwf.1, by rw [hBlen]; omega⟩
    $$ H0
  rw [List.append_nil]
  iexact Hput

theorem wp_WriteBytes (s : slice.t) (vs : List w8) (data_sl : slice.t) (q : DFrac) (data : List w8) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        data_sl ↦*{q} data ∗ own_slice_cap w8 s (DFrac.own 1) }}
      (App (App (Val (@! WriteBytes)) (Val #s)) (Val #data_sl))
    {{ (s' : slice.t), RET #s'; s' ↦* (vs ++ data) ∗ own_slice_cap w8 s' (DFrac.own 1) ∗
        data_sl ↦*{q} data }} := by
  wp_start as ⟨Hs, Hdata, Hcap⟩
  wp_auto
  wp_apply wp_slice_append (V := w8) (t := go.byte) s vs data_sl data q $$ [$Hs $Hcap $Hdata]
    as %s' ⟨Hs', Hcap', Hdata'⟩
  iapply HΦ
  iframe

theorem wp_WriteLenPrefixedBytes (s : slice.t) (vs : List w8) (data_sl : slice.t) (q : DFrac)
    (data : List w8) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        data_sl ↦*{q} data ∗ own_slice_cap w8 s (DFrac.own 1) }}
      (App (App (Val (@! WriteLenPrefixedBytes)) (Val #s)) (Val #data_sl))
    {{ (s' : slice.t), RET #s';
        s' ↦* (vs ++ u64_le (W64 data.length) ++ data) ∗ own_slice_cap w8 s' (DFrac.own 1) ∗
        data_sl ↦*{q} data }} := by
  wp_start as ⟨Hs, Hdata, Hscap⟩
  ihave %Hdlen := own_slice_len _ _ _ $$ Hdata
  wp_auto
  wp_apply wp_WriteInt s data_sl.len vs $$ [$Hs $Hscap] as %s' ⟨Hs', Hscap⟩
  wp_apply wp_WriteBytes s' _ data_sl q data $$ [$Hs' $Hdata $Hscap] as %s'0 ⟨Hs, Hscap, Hdata⟩
  iapply HΦ
  have : W64 (data.length : Int) = data_sl.len := by
    rw [Hdlen.1]; simp only [sint.nat, W64]
    rw [Int.toNat_of_nonneg Hdlen.2]; exact BitVec.ofInt_toInt
  rw [this, List.append_assoc]
  iframe

theorem arr_set_1 (x : w8) (kvs : List keyed_element) (h : go.array_literal_size kvs = 1) :
    (zero_val (array.t w8 (go.array_literal_size kvs))).arr.set (sint.nat (W64 0)) x = [x] := by
  revert h
  generalize go.array_literal_size kvs = n
  intro h; subst h; rfl

section no_slice_literal_step
-- Workaround (as in `unittest.lean`): `wp_auto` unfolds slice literals
-- (`composite_literal_slice` is a pure step), but `wp_slice_literal` expects
-- the literal to be folded.
attribute [-instance] go.SliceSemantics.composite_literal_slice

theorem wp_WriteBool (s : slice.t) (vs : List w8) (b : Bool) :
    {{ is_pkg_init (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        own_slice_cap w8 s (DFrac.own 1) }}
      (App (App (Val (@! WriteBool)) (Val #s)) (Val #b))
    {{ (s' : slice.t), RET #s'; s' ↦* (vs ++ [if b then W8 1 else W8 0]) ∗
        own_slice_cap w8 s' (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hcap⟩
  wp_auto
  cases b <;> (
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) s vs _ _ _ $$ [$Hs $Hcap $Hsl]
      as %s' ⟨Hs', Hcap', -⟩
    iapply HΦ
    iframe Hcap'
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [arr_set_1 _ _ (by rfl)]
    iexact Hs')

end no_slice_literal_step

end wps

end github_com.tchajed.marshal

end Perennial
end
