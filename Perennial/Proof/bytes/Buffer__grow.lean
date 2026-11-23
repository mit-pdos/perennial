/-
The proof of `bytes.Buffer.grow`.
-/
module

public import Perennial.Spec.bytes.Buffer__grow
public import Perennial.Spec.bytes.Buffer__Len
public import Perennial.Spec.bytes.Buffer__tryGrowByReslice
public import Perennial.Spec.bytes.growSlice

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- What `copy(b.buf, b.buf[b.off:])` leaves in `buf` (`wp_slice_copy_within`): its first
`len - off` bytes are the unread ones. -/
private theorem slide_contents (all : List w8) (z off len m : Nat) (hz : z = 0)
    (hlen : all.length = len) (hoff : off ≤ len) (hm : m = len - off) :
    m ≤ (all.take z ++ ((subslice off len all).take (len - z) ++
      (subslice z len all).drop (len - off)) ++ all.drop len).length ∧
    (all.take z ++ ((subslice off len all).take (len - z) ++
      (subslice z len all).drop (len - off)) ++ all.drop len).take m = all.drop off := by
  subst hz hm
  have h1 : (subslice off len all).take len = all.drop off := by
    simp only [subslice]
    rw [List.take_of_length_le (l := all) (by omega)]
    rw [List.take_of_length_le (by simp; omega)]
  simp only [List.take_zero, List.nil_append, Nat.sub_zero, h1, List.append_assoc]
  constructor
  · simp; omega
  · exact List.take_left' (by simp; omega)

theorem bytes.Buffer.grow.wp_proof
    (wp_Len : bytes.Buffer.Len.spec (GF := GF) (hG := hG))
    (wp_tryGrowByReslice : bytes.Buffer.tryGrowByReslice.spec (GF := GF) (hG := hG))
    (wp_growSlice : bytes.growSlice.spec (GF := GF) (hG := hG)) :
    bytes.Buffer.grow.spec (GF := GF) (hG := hG) := by
  intro l b all n
  wp_start as ⟨Hl, Hbuf, Hcap, %Hpre⟩
  wp_auto
  wp_apply wp_Len l b (DFrac.own 1) $$ [$Hl] as Hl
  ihave %Hlen := ownSlice_len $$ Hbuf
  ihave %Hwf := ownSlice_wf $$ Hbuf
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨bb, off, lr⟩ := b
  simp only at Hpre Hlen Hwf ⊢
  iStructNamed Hl
  -- `if m == 0 && b.off != 0 { b.Reset() }`: join with the buffer's unread bytes unchanged
  wp_join (iprop(∃ (b1 : bytes.Buffer) (all1 : List w8), b_ptr ↦ l ∗ l ↦ b1 ∗ b1.buf' ↦* all1 ∗
      ownSliceCap w8 b1.buf' (DFrac.own 1) ∗
      ⌜0 ≤ sint.Z b1.off' ∧ sint.nat b1.off' ≤ all1.length ∧
        all1.drop (sint.nat b1.off') = all.drop (sint.nat off) ∧
        b1.buf'.len - b1.off' = bb.len - off⌝) : IProp GF)
    with [b buf off lastRead Hbuf Hcap] as ⟨%b1, %all1, b, Hl, Hbuf, Hcap, %Hb1⟩
  · have Hm0' : bb.len - off = W64 0 := Hif
    have Hm0 : sint.Z bb.len = sint.Z off := by
      have := congrArg sint.Z Hif; word
    wp_if_destruct
    · wp_join_done
      iexists ⟨bb, W64 0, lr⟩, all
      iframe b Hbuf Hcap
      isplitl
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      exact ⟨Hpre.2.2.1, Hpre.2.2.2, rfl, rfl⟩
    · -- `b.Reset()`: `b.buf = b.buf[:0]`, `b.off = 0`
      wp_method_call
      wp_call
      wp_auto
      simp only [bytes.opInvalid]
      have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
          sint.Z (W64 0) ≤ sint.Z bb.cap := ⟨by decide, by decide, by word⟩
      simp only [Hb0, _root_.and_self, ↓reduceIte]
      wp_auto
      icases ownSlice_slice_with_cap (W64 0) (W64 0) bb all ⟨by decide, by decide, by word⟩
        $$ [$Hbuf $Hcap] with ⟨Hbuf, -, Hcap⟩
      wp_join_done
      iexists ⟨slice.slice bb w8 (W64 0) (W64 0), W64 0, W8 0⟩, all.take (sint.nat (W64 0))
      iframe b Hbuf Hcap
      isplitl
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      simp only [slice.slice]
      have h0 : sint.nat (W64 0) = 0 := rfl
      have hal : all.length ≤ sint.nat off := by
        have := Hlen.1; have : sint.nat bb.len = sint.nat off := by word
        omega
      refine ⟨by decide, by simp [h0], ?_, by rw [Hm0']; word⟩
      rw [List.drop_eq_nil_of_le hal]
      simp [h0]
  · iexists ⟨bb, off, lr⟩, all
    iframe b Hbuf Hcap
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    exact ⟨Hpre.2.2.1, Hpre.2.2.2, rfl, rfl⟩
  rw [← Hb1.2.2.1]
  wp_apply wp_tryGrowByReslice l b1 all1 n $$ [$Hl $Hbuf $Hcap] as %i %ok Hres
  · ipureintro; exact ⟨Hpre.1, Hb1.1, Hb1.2.1⟩
  cases ok
  rotate_left
  · -- the bytes fit: `return i`
    simp only [↓reduceIte]
    wp_auto
    iapply HΦ $$ Hres
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hres with ⟨%Hfit, Hl, Hbuf, Hcap⟩
  ihave %Hlb := ownSlice_bytes_len_le $$ Hbuf
  ihave %Hcb := ownSliceCap_bytes_le $$ Hcap
  ihave %Hlen1 := ownSlice_len $$ Hbuf
  ihave %Hwf1 := ownSlice_wf $$ Hbuf
  obtain ⟨bb1, off1, lr1⟩ := b1
  simp only at Hb1 Hfit Hlb Hcb Hlen1 Hwf1 ⊢
  unfold maxAddr at Hlb Hcb Hpre
  iStructNamed Hl
  wp_auto
  rw [← Hb1.2.2.2]
  by_cases hnil : bb1 = slice.nil
  · have Hall1 : all1 = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hlen1.1, hnil]; rfl
    have Hoff1 : off1 = W64 0 := by
      have := Hb1.2.1; rw [Hall1] at this; simp at this; word
    rw [decide_eq_true hnil]
    try simp only [_root_.decide_true, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · -- `b.buf = make([]byte, n, smallBufferSize)`, `return 0`
      wp_apply wp_slice_make3 (V := w8) n (W64 64) ⟨Hpre.1, by word⟩ as %nb ⟨Hbuf', Hcap', -⟩
      iapply HΦ
      unfold bytes.bufferGrown
      iexists ⟨nb, W64 0, lr1⟩, _
      iframe Hbuf' Hcap'
      isplitl
      · rw [← Hoff1]
        iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      subst Hall1 Hoff1
      simp
    · -- (`n > smallBufferSize`)
      try wp_auto
      wp_if_destruct
      · -- slide the unread bytes down: `copy(b.buf, b.buf[b.off:])`
        have hcopy := wp_slice_copy_within (GF := GF) (st := go.GoType.SliceType go.byte) (t := go.byte)
          (V := w8) bb1 all1 (W64 0) bb1.len off1 bb1.len ⟨by decide, by word, by word⟩
          ⟨Hb1.1, by word, by word⟩ (s := .NotStuck) (E := ⊤)
        rw [← slice_slice_trivial] at hcopy
        have Hbs : 0 ≤ sint.Z off1 ∧ sint.Z off1 ≤ sint.Z bb1.len ∧ sint.Z bb1.len ≤ sint.Z bb1.cap :=
          ⟨Hb1.1, by word, Hwf1.2⟩
        simp only [Hbs, _root_.and_self, ↓reduceIte]
        wp_apply hcopy $$ [$Hbuf] as %k ⟨-, Hbuf⟩
        try rw [show sint.nat (W64 0) = 0 from rfl]
        obtain ⟨Hnm, Hm⟩ := slide_contents all1 0 (sint.nat off1) (sint.nat bb1.len)
          (sint.nat (bb1.len - off1)) rfl Hlen1.1 (by word) (by word)
        have Hcapm : sint.Z (bb1.len - off1) + sint.Z n ≤ sint.Z bb1.cap := by word
        try wp_auto
        have h00 : sint.Z (W64 0) = 0 := rfl
        have HM : sint.Z (bb1.len - off1) = sint.Z bb1.len - sint.Z off1 := by word
        have Hmn' : sint.Z ((bb1.len - off1) + n) = sint.Z (bb1.len - off1) + sint.Z n := by word
        have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z ((bb1.len - off1) + n) ∧
            sint.Z ((bb1.len - off1) + n) ≤ sint.Z (bb1).cap := ⟨by decide, by omega, by omega⟩
        simp only [Hb, _root_.and_self, ↓reduceIte]
        icases ownSlice_reslice (bb1) _ ((bb1.len - off1) + n) ⟨by omega, by omega⟩ $$ [$Hbuf $Hcap]
          with ⟨%nall', Hbuf, Hcap, %Htk⟩
        ihave %Hlen' := ownSlice_len $$ Hbuf
        try wp_auto
        iapply HΦ
        unfold bytes.bufferGrown
        iexists ⟨slice.slice (bb1) w8 (W64 0) ((bb1.len - off1) + n), W64 0, lr1⟩, nall'
        iframe Hbuf Hcap
        isplitl
        · iapply typedPointsto_combine _ _ _ Hnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ipureintro
        simp only [slice.slice] at Hlen' ⊢
        refine ⟨by decide, by word, ?_, ?_⟩
        · rw [Hlen'.1]; word
        · have hmn : sint.nat (bb1.len - off1) ≤ sint.nat ((bb1.len - off1) + n) := by word
          have e := congrArg (List.take (sint.nat (bb1.len - off1))) Htk
          rw [List.take_take, List.take_take, Nat.min_eq_left Hnm, Nat.min_eq_left hmn] at e
          rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, e, Hm]

      · wp_if_destruct
        · exfalso; unfold bytes.maxInt at *; word
        -- `b.buf = growSlice(b.buf[b.off:], b.off+n)`
        have Hb : 0 ≤ sint.Z off1 ∧ sint.Z off1 ≤ sint.Z bb1.len ∧ sint.Z bb1.len ≤ sint.Z bb1.cap :=
          ⟨Hb1.1, by word, Hwf1.2⟩
        simp only [Hb, _root_.and_self, ↓reduceIte]
        icases (ownSlice_split_all off1 bb1 _ _ ⟨Hb1.1, by word⟩).1 $$ Hbuf with ⟨-, Hbuf2⟩
        try wp_auto
        wp_apply wp_growSlice $$ [$Hbuf2] as %nb ⟨-, Hbuf, Hcap', %Hnb⟩
        · ipureintro; simp only [slice.slice]; unfold maxAddr; refine ⟨by word, by word, by word⟩
        iclear Hcap
        irename Hcap' => Hcap
        have Hnm : sint.nat (bb1.len - off1) ≤ (all1.drop (sint.nat off1)).length := by
          rw [List.length_drop, Hlen1.1]; word
        have Hm : (all1.drop (sint.nat off1)).take (sint.nat (bb1.len - off1)) = all1.drop (sint.nat off1) := by
          apply List.take_of_length_le; rw [List.length_drop, Hlen1.1]; word
        have Hcapm : sint.Z (bb1.len - off1) + sint.Z n ≤ sint.Z nb.cap := by
          simp only [slice.slice] at Hnb; word
        try wp_auto
        have h00 : sint.Z (W64 0) = 0 := rfl
        have HM : sint.Z (bb1.len - off1) = sint.Z bb1.len - sint.Z off1 := by word
        have Hmn' : sint.Z ((bb1.len - off1) + n) = sint.Z (bb1.len - off1) + sint.Z n := by word
        have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z ((bb1.len - off1) + n) ∧
            sint.Z ((bb1.len - off1) + n) ≤ sint.Z (nb).cap := ⟨by decide, by omega, by omega⟩
        simp only [Hb, _root_.and_self, ↓reduceIte]
        icases ownSlice_reslice (nb) _ ((bb1.len - off1) + n) ⟨by omega, by omega⟩ $$ [$Hbuf $Hcap]
          with ⟨%nall', Hbuf, Hcap, %Htk⟩
        ihave %Hlen' := ownSlice_len $$ Hbuf
        try wp_auto
        iapply HΦ
        unfold bytes.bufferGrown
        iexists ⟨slice.slice (nb) w8 (W64 0) ((bb1.len - off1) + n), W64 0, lr1⟩, nall'
        iframe Hbuf Hcap
        isplitl
        · iapply typedPointsto_combine _ _ _ Hnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ipureintro
        simp only [slice.slice] at Hlen' ⊢
        refine ⟨by decide, by word, ?_, ?_⟩
        · rw [Hlen'.1]; word
        · have hmn : sint.nat (bb1.len - off1) ≤ sint.nat ((bb1.len - off1) + n) := by word
          have e := congrArg (List.take (sint.nat (bb1.len - off1))) Htk
          rw [List.take_take, List.take_take, Nat.min_eq_left Hnm, Nat.min_eq_left hmn] at e
          rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, e, Hm]


  · rw [decide_eq_false hnil]
    try simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · -- slide the unread bytes down: `copy(b.buf, b.buf[b.off:])`
      have hcopy := wp_slice_copy_within (GF := GF) (st := go.GoType.SliceType go.byte) (t := go.byte)
        (V := w8) bb1 all1 (W64 0) bb1.len off1 bb1.len ⟨by decide, by word, by word⟩
        ⟨Hb1.1, by word, by word⟩ (s := .NotStuck) (E := ⊤)
      rw [← slice_slice_trivial] at hcopy
      have Hbs : 0 ≤ sint.Z off1 ∧ sint.Z off1 ≤ sint.Z bb1.len ∧ sint.Z bb1.len ≤ sint.Z bb1.cap :=
        ⟨Hb1.1, by word, Hwf1.2⟩
      simp only [Hbs, _root_.and_self, ↓reduceIte]
      wp_apply hcopy $$ [$Hbuf] as %k ⟨-, Hbuf⟩
      try rw [show sint.nat (W64 0) = 0 from rfl]
      obtain ⟨Hnm, Hm⟩ := slide_contents all1 0 (sint.nat off1) (sint.nat bb1.len)
        (sint.nat (bb1.len - off1)) rfl Hlen1.1 (by word) (by word)
      have Hcapm : sint.Z (bb1.len - off1) + sint.Z n ≤ sint.Z bb1.cap := by word
      try wp_auto
      have h00 : sint.Z (W64 0) = 0 := rfl
      have HM : sint.Z (bb1.len - off1) = sint.Z bb1.len - sint.Z off1 := by word
      have Hmn' : sint.Z ((bb1.len - off1) + n) = sint.Z (bb1.len - off1) + sint.Z n := by word
      have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z ((bb1.len - off1) + n) ∧
          sint.Z ((bb1.len - off1) + n) ≤ sint.Z (bb1).cap := ⟨by decide, by omega, by omega⟩
      simp only [Hb, _root_.and_self, ↓reduceIte]
      icases ownSlice_reslice (bb1) _ ((bb1.len - off1) + n) ⟨by omega, by omega⟩ $$ [$Hbuf $Hcap]
        with ⟨%nall', Hbuf, Hcap, %Htk⟩
      ihave %Hlen' := ownSlice_len $$ Hbuf
      try wp_auto
      iapply HΦ
      unfold bytes.bufferGrown
      iexists ⟨slice.slice (bb1) w8 (W64 0) ((bb1.len - off1) + n), W64 0, lr1⟩, nall'
      iframe Hbuf Hcap
      isplitl
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      simp only [slice.slice] at Hlen' ⊢
      refine ⟨by decide, by word, ?_, ?_⟩
      · rw [Hlen'.1]; word
      · have hmn : sint.nat (bb1.len - off1) ≤ sint.nat ((bb1.len - off1) + n) := by word
        have e := congrArg (List.take (sint.nat (bb1.len - off1))) Htk
        rw [List.take_take, List.take_take, Nat.min_eq_left Hnm, Nat.min_eq_left hmn] at e
        rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, e, Hm]

    · wp_if_destruct
      · exfalso; unfold bytes.maxInt at *; word
      -- `b.buf = growSlice(b.buf[b.off:], b.off+n)`
      have Hb : 0 ≤ sint.Z off1 ∧ sint.Z off1 ≤ sint.Z bb1.len ∧ sint.Z bb1.len ≤ sint.Z bb1.cap :=
        ⟨Hb1.1, by word, Hwf1.2⟩
      simp only [Hb, _root_.and_self, ↓reduceIte]
      icases (ownSlice_split_all off1 bb1 _ _ ⟨Hb1.1, by word⟩).1 $$ Hbuf with ⟨-, Hbuf2⟩
      try wp_auto
      wp_apply wp_growSlice $$ [$Hbuf2] as %nb ⟨-, Hbuf, Hcap', %Hnb⟩
      · ipureintro; simp only [slice.slice]; unfold maxAddr; refine ⟨by word, by word, by word⟩
      iclear Hcap
      irename Hcap' => Hcap
      have Hnm : sint.nat (bb1.len - off1) ≤ (all1.drop (sint.nat off1)).length := by
          rw [List.length_drop, Hlen1.1]; word
      have Hm : (all1.drop (sint.nat off1)).take (sint.nat (bb1.len - off1)) = all1.drop (sint.nat off1) := by
        apply List.take_of_length_le; rw [List.length_drop, Hlen1.1]; word
      have Hcapm : sint.Z (bb1.len - off1) + sint.Z n ≤ sint.Z nb.cap := by
        simp only [slice.slice] at Hnb; word
      try wp_auto
      have h00 : sint.Z (W64 0) = 0 := rfl
      have HM : sint.Z (bb1.len - off1) = sint.Z bb1.len - sint.Z off1 := by word
      have Hmn' : sint.Z ((bb1.len - off1) + n) = sint.Z (bb1.len - off1) + sint.Z n := by word
      have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z ((bb1.len - off1) + n) ∧
          sint.Z ((bb1.len - off1) + n) ≤ sint.Z (nb).cap := ⟨by decide, by omega, by omega⟩
      simp only [Hb, _root_.and_self, ↓reduceIte]
      icases ownSlice_reslice (nb) _ ((bb1.len - off1) + n) ⟨by omega, by omega⟩ $$ [$Hbuf $Hcap]
        with ⟨%nall', Hbuf, Hcap, %Htk⟩
      ihave %Hlen' := ownSlice_len $$ Hbuf
      try wp_auto
      iapply HΦ
      unfold bytes.bufferGrown
      iexists ⟨slice.slice (nb) w8 (W64 0) ((bb1.len - off1) + n), W64 0, lr1⟩, nall'
      iframe Hbuf Hcap
      isplitl
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      simp only [slice.slice] at Hlen' ⊢
      refine ⟨by decide, by word, ?_, ?_⟩
      · rw [Hlen'.1]; word
      · have hmn : sint.nat (bb1.len - off1) ≤ sint.nat ((bb1.len - off1) + n) := by word
        have e := congrArg (List.take (sint.nat (bb1.len - off1))) Htk
        rw [List.take_take, List.take_take, Nat.min_eq_left Hnm, Nat.min_eq_left hmn] at e
        rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, e, Hm]



end proof

end Perennial
