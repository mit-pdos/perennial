/-
Results of `bytes` derived from the linked ones: a `*Buffer` keeps the reader contract
(`bytes.wp_buffer_readerOk`), and `io.MultiReader` of a `*Buffer` and another reader
(`bytes.wp_MultiReader_buffer`) reads the buffer's bytes, then the reader's stream.
-/
module

public import Perennial.Proof.bytes.Link
public import Perennial.Proof.bytes.BufferReader
public import Perennial.Proof.io.Results

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- **A `*Buffer` `l` holding `bs` is an `io.Reader` of the stream `bs`**: it keeps the reader
contract (`io.readerOk`) with the state `bytes.bufferReadState l bs` and the errors
`bytes.bufferReadErr bs eof` (`io.EOF`, once all of `bs` is delivered). -/
theorem bytes.wp_buffer_readerOk (l : Loc) (bs : List w8) (eof : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ⊢
      io.readerOk ⟨go.GoType.PointerType bytes.Buffer.ty, #l⟩ (fun _ _ => True)
        (bytes.bufferReadState l bs) (bytes.bufferReadErr bs eof) :=
  bytes.buffer_readerOk bytes.Buffer.wp_Read l bs eof

/-- A `*Buffer` `l` holding `pre`, as a reader of `io.MultiReader` (`io.ReaderC`): its reader
contract is `bytes.wp_buffer_readerOk`'s. -/
abbrev bytes.bufferReaderC (l : Loc) (pre : List w8) (eof : GoInterface) : io.ReaderC GF :=
  ⟨⟨go.GoType.PointerType bytes.Buffer.ty, #l⟩, bytes.bufferReadState l pre,
    bytes.bufferReadErr pre eof⟩

theorem bytes.buffer_ne_multiReader :
    go.GoType.PointerType bytes.Buffer.ty ≠ go.GoType.PointerType io.multiReader.ty := by
  unfold bytes.Buffer.ty io.multiReader.ty
  intro h; injection h with h1; injection h1 with h2; simp at h2

/-- **`io.MultiReader(buf, rc)`** of a `*Buffer` `l` holding `pre` and a reader `rc` keeping
the contract `io.readerOkOut Out` (`Out` allowing what a `*Buffer`'s `Read` does to its buffer,
`io.keepOut`; `io.scratchOut` does), from its initial state: a `*multiReader` `m` keeping the same
contract over the two readers, in its initial state. What it delivers is described by
`bytes.mrState_buffer_prefix` (comparable with `pre`) and `bytes.mrErr_buffer_eof` (at `EOF`,
`pre` followed by a complete stream of `rc`). -/
theorem bytes.wp_MultiReader_buffer (Out : io.ReadOut) (hOut : io.OutLaw Out)
    (hkeep : ∀ xs ys c, ys.length ≤ xs.length → io.keepOut xs ys c → Out xs ys c)
    (sl : GoSlice) (dq : DFrac) (l : Loc) (pre : List w8) (rc : io.ReaderC GF)
    (eof : GoInterface) (hrc : rc.ri.ty ≠ go.GoType.PointerType io.multiReader.ty) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ∗
        sl ↦*{dq} [interface.mkOk (go.GoType.PointerType bytes.Buffer.ty) #l, rc.iface] ∗
        bytes.ownBuffer l pre ∗ io.readerOkOut Out rc.ri rc.S rc.E ∗ rc.S [] }}
      (App (Val (@! io.MultiReader)) (Val #sl))
    {{ (m : Loc), RET #(interface.mkOk (go.GoType.PointerType io.multiReader.ty) #m);
        sl ↦*{dq} [interface.mkOk (go.GoType.PointerType bytes.Buffer.ty) #l, rc.iface] ∗
        io.readerOkOut Out ⟨go.GoType.PointerType io.multiReader.ty, #m⟩
          (io.mrState m [bytes.bufferReaderC l pre eof, rc] eof)
          (io.mrErr [bytes.bufferReaderC l pre eof, rc] eof) ∗
        io.mrState m [bytes.bufferReaderC l pre eof, rc] eof [] }} := by
  iintro %Φ ⟨#Hinit, #Heof, Hsl, Hb, #Hrc, HS⟩ HΦ
  ihave #Hbr := bytes.wp_buffer_readerOk l pre eof $$ [Hinit Heof]
  · iframe Hinit Heof
  ihave #Hbo := io.readerOkOut_of_readerOk _ _ _ $$ Hbr
  ihave #Hbo' := io.readerOkOut_mono io.keepOut Out _ _ _ hkeep $$ Hbo
  ihave #Hrs : (□ ∀ c, ⌜c ∈ [bytes.bufferReaderC l pre eof, rc]⌝ -∗
      io.readerOkOut Out c.ri c.S c.E : IProp GF) $$ []
  · imodintro
    iintro %c %hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · iexact Hbo'
    · iexact Hrc
  have hty : ∀ c ∈ [bytes.bufferReaderC l pre eof, rc],
      c.ri.ty ≠ go.GoType.PointerType io.multiReader.ty := by
    intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact bytes.buffer_ne_multiReader
    · exact hrc
  have hmap : List.map io.ReaderC.iface [bytes.bufferReaderC l pre eof, rc] =
      [interface.mkOk (go.GoType.PointerType bytes.Buffer.ty) #l, rc.iface] := rfl
  iapply io.wp_MultiReader sl dq [bytes.bufferReaderC l pre eof, rc] eof $$ [Hsl Hb HS]
  · rw [hmap]
    iframe Hsl
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hb]
    · simp only [bytes.bufferReaderC, bytes.bufferReadState]
      isplitr
      · ipureintro; exact List.nil_prefix
      · simp only [List.length_nil, List.drop_zero]; iexact Hb
    iapply BigSepL.bigSepL_cons.2
    iframe HS
    iapply BigSepL.bigSepL_nil.2
    itrivial
  inext
  iintro %m ⟨Hsl, Hst⟩
  rw [hmap]
  iapply HΦ
  iframe Hsl Hst
  iapply io.multiReader_readerOkOut Out _ eof m hOut hty
  iframe Hinit Heof Hrs

/-- What a `MultiReader` of a buffer holding `pre` and `rc` has delivered is comparable with
`pre`. -/
theorem bytes.mrState_buffer_prefix (m l : Loc) (pre : List w8) (rc : io.ReaderC GF)
    (eof : GoInterface) (r : List w8) :
    io.mrState m [bytes.bufferReaderC l pre eof, rc] eof r ⊢
      ⌜r <+: pre ∨ pre <+: r⌝ ∗ io.mrState m [bytes.bufferReaderC l pre eof, rc] eof r := by
  iintro Hst
  unfold io.mrState
  icases Hst with ⟨%done, %rem, %sl, %cur, %Hcs, Hl, Hsl, #Hdone, Hcur⟩
  obtain ⟨Hcs, Hr⟩ := Hcs
  ihave %Hp : ⌜r <+: pre ∨ pre <+: r⌝ $$ [Hcur]
  · rcases done with _ | ⟨d1, done⟩
    · simp only [List.map_nil, List.nil_append] at Hcs
      subst Hcs
      rw [io.mrCur_cons]
      simp only [bytes.bufferReadState]
      icases Hcur with ⟨⟨%h, -⟩, -⟩
      ipureintro; left; simpa [Hr] using h
    · unfold io.mrDone
      ihave Hd := Hdone $$ %d1 %(List.mem_cons_self)
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at Hcs
      obtain ⟨h1, -⟩ := Hcs
      rw [← h1]
      simp only [bytes.bufferReadErr]
      icases Hd with %hd
      ipureintro; right
      rw [Hr, List.map_cons, List.flatten_cons, hd.1, List.append_assoc]
      exact List.prefix_append _ _
  isplitr
  · ipureintro; exact Hp
  iexists done, rem, sl, cur
  iframe Hl Hsl Hdone Hcur
  ipureintro; exact ⟨Hcs, Hr⟩

/-- At `EOF`, a `MultiReader` of a buffer holding `pre` and `rc` has delivered `pre` followed by
a complete stream `t` of `rc` (with `rc`'s evidence of its `EOF`). -/
theorem bytes.mrErr_buffer_eof (l : Loc) (pre : List w8) (rc : io.ReaderC GF)
    (eof : GoInterface) (r : List w8) :
    io.mrErr [bytes.bufferReaderC l pre eof, rc] eof r eof ⊢
      ∃ t, ⌜r = pre ++ t⌝ ∗ □ rc.E t eof := by
  unfold io.mrErr
  iintro (⟨%done, %c, %rem, %cur, %h, -⟩ | ⟨%done, %h, #Hdone⟩)
  · exact absurd rfl h.1
  obtain ⟨-, Hcs, Hr⟩ := h
  rcases done with _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, done⟩⟩⟩
  · simp at Hcs
  · simp at Hcs
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at Hcs
    obtain ⟨h1, h2⟩ := Hcs
    unfold io.mrDone
    ihave Hd1 := Hdone $$ %d1 %(List.mem_cons_self)
    ihave Hd2 := Hdone $$ %d2 %(List.mem_cons_of_mem _ List.mem_cons_self)
    rw [← h1]
    simp only [bytes.bufferReadErr]
    icases Hd1 with %hd
    iexists d2.2
    rw [← h2]
    iframe Hd2
    ipureintro
    simp [Hr, hd.1]
  · simp at Hcs

end results

end Perennial
