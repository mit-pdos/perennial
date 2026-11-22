/-
Shared definitions of the proofs of `bytes.Buffer`: `bytes.ownBuffer l bs`, a `*Buffer` whose
unread content is `bs`, and the reader contract (`io.readerOk`) a `*Buffer` keeps when read.
-/
module

public import Perennial.Proof.bytes.Base
public import Perennial.Proof.io.Reader
public import Perennial.Golang.Theory.Plain

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace bytes

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- **The `*Buffer` at `l` holds the unread bytes `bs`** (exclusive): its slice `buf` holds
`all`, with `buf`'s spare capacity (which `Write` grows into), and its read offset `off` is
within it, with `bs = all[off:]` (`bytes.Buffer`'s comment: "contents are the bytes
buf[off : len(buf)]"). -/
def ownBuffer (l : Loc) (bs : List w8) : IProp GF :=
  iprop(∃ (b : Buffer) (all : List w8), l ↦ b ∗ b.buf' ↦* all ∗
    ownSliceCap w8 b.buf' (DFrac.own 1) ∗
    ⌜0 ≤ sint.Z b.off' ∧ sint.nat b.off' ≤ all.length ∧ bs = all.drop (sint.nat b.off')⌝)

/-- **A zero `Buffer` is empty** (what `&bytes.Buffer{}` or `new(bytes.Buffer)` allocates): its
`buf` is the nil slice, its offset 0. -/
theorem ownBuffer_new (l : Loc) :
    l ↦ (zero_val Buffer) ⊢ ownBuffer (GF := GF) l [] := by
  iintro Hb
  unfold ownBuffer
  ihave Hs := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hc := ownSliceCap_nil (V := w8) (GF := GF)
  have hbuf : (zero_val Buffer).buf' = slice.nil := rfl
  have hoff : (zero_val Buffer).off' = 0 := rfl
  iexists (zero_val Buffer), []
  rw [hbuf, hoff]
  iframe Hb Hs Hc
  ipureintro
  exact ⟨by decide, by decide, rfl⟩

/-- The `*Buffer` at `l` after growing it for `n` more bytes at the index `i` (what
`tryGrowByReslice` and `grow` leave, for `Write` to copy into `buf[i:]`): `buf` holds `i + n`
bytes, of which `buf[off:i]` are the unread bytes `bs`, with its spare capacity. -/
def bufferGrown (l : Loc) (bs : List w8) (i n : w64) : IProp GF :=
  iprop(∃ (b : Buffer) (all : List w8), l ↦ b ∗ b.buf' ↦* all ∗
    ownSliceCap w8 b.buf' (DFrac.own 1) ∗
    ⌜0 ≤ sint.Z b.off' ∧ sint.Z b.off' ≤ sint.Z i ∧ all.length = sint.nat i + sint.nat n ∧
      (all.take (sint.nat i)).drop (sint.nat b.off') = bs⌝)

/-- The state of a `*Buffer` `l` read as a stream of `bs` (`io.readerOk`'s `S`): having
delivered `r`, a prefix of `bs`, it holds the rest. -/
def bufferReadState (l : Loc) (bs : List w8) (r : List w8) : IProp GF :=
  iprop(⌜r <+: bs⌝ ∗ ownBuffer l (bs.drop r.length))

/-- What an error of a `*Buffer` read as a stream of `bs` says (`io.readerOk`'s `E`): it is
`io.EOF` (`eof`), returned only once all of `bs` has been delivered. -/
def bufferReadErr (bs : List w8) (eof : GoInterface) (r : List w8) (e : GoInterface) : IProp GF :=
  iprop(⌜r = bs ∧ e = eof⌝)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
open Iris.ProofMode

/-- An owned byte slice is at most `maxAddr` long: its bytes are at distinct addresses in
`(0, maxAddr]` (`typedPointsto_byte_array_bounds`). -/
theorem ownSlice_bytes_len_le (s : GoSlice) (dq : DFrac) (bs : List w8) :
    (s ↦*{dq} bs : IProp GF) ⊢ ⌜sint.Z s.len ≤ maxAddr⌝ := by
  iintro Hs
  ihave %Hlen := ownSlice_len $$ Hs
  by_cases h : bs = []
  · subst h
    ipureintro
    simp only [List.length_nil] at Hlen
    unfold maxAddr
    have : sint.Z s.len = 0 := by
      have h1 := Hlen.1; word
    omega
  rw [ownSlice_unseal]; unfold ownSliceDef
  icases Hs with (%H | ⟨H, %_⟩)
  · exact absurd H.2 h
  icases typedPointsto_byte_array_bounds _ _ (array.mk (sint.Z s.len) bs) dq h $$ H with %Hb
  ipureintro; omega

/-- An owned byte capacity is at most `maxAddr` long (as `ownSlice_bytes_len_le`). -/
theorem ownSliceCap_bytes_le (s : GoSlice) (dq : DFrac) :
    ownSliceCap (GF := GF) w8 s dq ⊢ ⌜sint.Z s.cap - sint.Z s.len ≤ maxAddr⌝ := by
  rw [ownSliceCap_unseal]; unfold ownSliceCapDef
  iintro (%H | ⟨%H, %a, Ha⟩)
  · ipureintro; rw [H.2.2]; unfold maxAddr; omega
  · obtain ⟨arr⟩ := a
    by_cases h : arr = []
    · subst h
      icases array_len _ _ _ _ $$ Ha with %Hl
      ipureintro; simp only [List.length_nil] at Hl; unfold maxAddr; omega
    · icases typedPointsto_byte_array_bounds _ _ (array.mk _ arr) dq h $$ Ha with %Hb
      ipureintro; omega

/-- An owned byte slice with its capacity has a capacity of at most `2 * maxAddr`. -/
theorem ownSlice_bytes_cap_le (s : GoSlice) (bs : List w8) (dq dq' : DFrac) :
    (s ↦*{dq} bs ∗ ownSliceCap w8 s dq' : IProp GF) ⊢ ⌜sint.Z s.cap ≤ 2 * maxAddr⌝ := by
  iintro ⟨Hs, Hc⟩
  ihave %H1 := ownSlice_bytes_len_le $$ Hs
  ihave %H2 := ownSliceCap_bytes_le $$ Hc
  ipureintro; omega

/-- Reslicing `s` to `s[:high]` within its capacity: the new slice's first `len(s)` elements
are `s`'s (as far as it goes), the rest arbitrary, and it keeps the capacity. -/
theorem ownSlice_reslice {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : GoSlice) (vs : List V) (high : w64)
    (hb : 0 ≤ sint.Z high ∧ sint.Z high ≤ sint.Z s.cap) :
    (s ↦* vs ∗ ownSliceCap V s (DFrac.own 1) : IProp GF) ⊢
      ∃ vs' : List V, slice.slice s V (W64 0) high ↦* vs' ∗
        ownSliceCap V (slice.slice s V (W64 0) high) (DFrac.own 1) ∗
        ⌜vs'.take vs.length = vs.take (sint.nat high)⌝ := by
  iintro ⟨Hs, Hc⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  by_cases h : sint.Z high ≤ sint.Z s.len
  · icases ownSlice_slice_with_cap (W64 0) high s vs ⟨by decide, by word, h⟩ $$ [$Hs $Hc]
      with ⟨-, Hs, Hc⟩
    iexists _
    iframe Hs Hc
    ipureintro
    simp only [subslice, show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    rw [List.take_take]
    have : (sint.nat high : Int) = sint.Z high := by word
    have : (sint.nat s.len : Int) = sint.Z s.len := by word
    congr 1; omega
  · icases ownSlice_slice_into_capacity (W64 0) high s vs $$ [$Hs $Hc] with ⟨%vc, -, Hs, Hc⟩
    · ipureintro; exact ⟨by decide, hb.1, by omega, hb.2⟩
    iexists _
    iframe Hs Hc
    ipureintro
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, List.take_left]
    have : (sint.nat high : Int) = sint.Z high := by word
    have : (sint.nat s.len : Int) = sint.Z s.len := by word
    rw [List.take_of_length_le (by omega)]

end lemmas

end bytes

end Perennial
