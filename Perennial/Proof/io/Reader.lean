/-
**An `io.Reader` and its contract**: the vocabulary of the specs of `io.ReadAtLeast`,
`io.ReadFull` and `io.ReadAll`, and of a reader meeting it (`(*bytes.Buffer).Read`).

* `io.readerOk ri Pre S E` (persistent): `ri.Read(p)`, from the state `S r` (`r` the bytes it
  has delivered so far), delivers the next `n` bytes `ys` into the front of `p`, with
  `0 ≤ n ≤ len(p)` (`io.Reader`'s contract, `io/io.go`: "0 <= n <= len(p)"), leaves
  `S (r ++ ys)`, and returns `nil` or an error with the evidence `E (r ++ ys)` gives of it
  (`io.errAt`), a well-typed one (`io.ptrTyped`). The bytes of `p` past `n` are unchanged. The client chooses `S` (what the bytes
  are), `E` (what an error means there: `io.EOF` only at the end, ...) and `Pre`, a condition on
  each call, on the bytes read so far and `len(p)` (a reader whose model bounds the offsets it
  reads at, say).
* `io.readAtLeastRes`, `io.readFullRes`: what `ReadAtLeast` and `ReadFull` return after
  delivering `ys`: enough bytes and `nil`, or fewer and the reader's last error (with its
  evidence), `io.ErrUnexpectedEOF` in place of `io.EOF` when some bytes came first.
-/
module

public import Perennial.Proof.io.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace io

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `err` is `nil`, or an error with the evidence `E r err` (persistently). -/
def errAt (E : List w8 → GoInterface → IProp GF) (r : List w8) (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ □ E r err)

instance errAt_persistent (E : List w8 → GoInterface → IProp GF) (r : List w8)
    (err : GoInterface) : Persistent (errAt E r err) := by
  unfold errAt; infer_instance

/-- `e`'s value is a pointer if its dynamic type is a pointer type: Go's typing, which the model
(with no typing of interface values) does not have. What comparing `e` with a pointer error
(`err == io.EOF`, an `*errorString`) needs to step. -/
def ptrTyped (e : GoInterface) : Prop :=
  ∀ (ii : GoInterfaceOk) (T : go.GoType), e = interface.ok ii → ii.ty = go.PointerType T →
    ∃ l : Loc, ii.v = #l

theorem ptrTyped_nil : ptrTyped interface.nil := by
  intro ii T h; cases h

/-- **`ri` reads by the contract `Pre`, `S`, `E`** (see the file header). -/
def readerOk (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (r : List w8) (p : GoSlice) (xs : List w8),
    {{ ⌜Pre r xs.length⌝ ∗ S r ∗ p ↦* xs }}
      (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ S (r ++ ys) ∗ errAt E (r ++ ys) err ∗
          ⌜ptrTyped err⌝ }})

instance readerOk_persistent (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF) :
    Persistent (readerOk ri Pre S E) := by
  unfold readerOk; infer_instance

/-- A call of `Read`, with `readerOk` kept folded in the caller's context. -/
theorem wp_reader_Read (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF) (r : List w8) (p : GoSlice)
    (xs : List w8) (hpre : Pre r xs.length) :
    {{ readerOk ri Pre S E ∗ S r ∗ p ↦* xs }}
      (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
          p ↦* (ys ++ xs.drop ys.length) ∗ S (r ++ ys) ∗ errAt E (r ++ ys) err ∗
          ⌜ptrTyped err⌝ }} := by
  iintro %Φ ⟨#Hr, HS, Hp⟩ HΦ
  unfold readerOk
  iapply Hr $$ %r %p %xs [HS Hp] HΦ
  iframe HS Hp
  ipureintro; exact hpre

/-- A contract with a weaker condition on each call: a reader meets it. -/
theorem readerOk_mono (ri : GoInterfaceOk) (Pre Pre' : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (h : ∀ r m, Pre' r m → Pre r m) :
    readerOk ri Pre S E ⊢ readerOk ri Pre' S E := by
  iintro #Hr
  unfold readerOk
  imodintro
  iintro %r %p %xs %Φ
  imodintro
  iintro ⟨%hpre, HS, Hp⟩ HΦ
  iapply Hr $$ %r %p %xs [HS Hp] HΦ
  iframe HS Hp
  ipureintro; exact h _ _ hpre

/-- **What a `Read` leaves in its buffer**, a relation `Out xs ys c` between the buffer's
contents `xs` before the call, the bytes `ys` delivered and its contents `c` after. A law of it
(`io.OutLaw`) is what passing the buffer on to another reader needs (`io.MultiReader`). -/
abbrev ReadOut := List w8 → List w8 → List w8 → Prop

/-- The bytes past those delivered are unchanged (`io.readerOk`'s promise). -/
def keepOut : ReadOut := fun xs ys c => c = ys ++ xs.drop ys.length

/-- The bytes past those delivered are arbitrary, the length unchanged: all `io.Reader`
promises ("Even if Read returns n < len(p), it may use all of p as scratch space during the
call", `io/io.go`). -/
def scratchOut : ReadOut := fun xs ys c => ys <+: c ∧ c.length = xs.length

/-- The laws of a `ReadOut` that `MultiReader` needs: an empty read may change the buffer (and
a reader may then be followed by another, reading into the changed buffer), but not its length,
and a call that does nothing is allowed. -/
structure OutLaw (Out : ReadOut) : Prop where
  refl : ∀ (xs : List w8), Out xs [] xs
  len : ∀ (xs c : List w8), Out xs [] c → c.length = xs.length
  comp : ∀ (xs c ys c' : List w8), Out xs [] c → Out c ys c' → Out xs ys c'

theorem keepOut_law : OutLaw keepOut where
  refl xs := by simp [keepOut]
  len xs c h := by simp [keepOut] at h; rw [h]
  comp xs c ys c' h1 h2 := by simp [keepOut] at h1; subst h1; exact h2

theorem scratchOut_law : OutLaw scratchOut where
  refl _ := ⟨List.nil_prefix, rfl⟩
  len _ _ h := h.2
  comp _ _ _ _ h1 h2 := ⟨h2.1, h2.2.trans h1.2⟩

theorem keepOut_scratchOut (xs ys c : List w8) (hl : ys.length ≤ xs.length) (h : keepOut xs ys c) :
    scratchOut xs ys c := by
  unfold keepOut at h; subst h
  refine ⟨List.prefix_append _ _, ?_⟩
  simp only [List.length_append, List.length_drop]; omega

/-- **`ri` reads by the contract `S`, `E`, leaving its buffer as `Out` says**: as
`io.readerOk` with no condition on the calls, but with `Out` in place of "the bytes of `p` past
`n` are unchanged" (`keepOut`). -/
def readerOkOut (Out : ReadOut) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (r : List w8) (p : GoSlice) (xs : List w8),
    {{ S r ∗ p ↦* xs }}
      (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys c : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧ Out xs ys c⌝ ∗
          p ↦* c ∗ S (r ++ ys) ∗ errAt E (r ++ ys) err ∗ ⌜ptrTyped err⌝ }})

instance readerOkOut_persistent (Out : ReadOut) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : Persistent (readerOkOut Out ri S E) := by
  unfold readerOkOut; infer_instance

/-- A contract that allows more of the buffer: a reader meets it. -/
theorem readerOkOut_mono (Out Out' : ReadOut) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF)
    (h : ∀ xs ys c, ys.length ≤ xs.length → Out xs ys c → Out' xs ys c) :
    readerOkOut Out ri S E ⊢ readerOkOut Out' ri S E := by
  iintro #Hr
  unfold readerOkOut
  imodintro
  iintro %r %p %xs %Φ
  imodintro
  iintro ⟨HS, Hp⟩ HΦ
  iapply Hr $$ %r %p %xs [HS Hp]
  · iframe
  inext
  iintro %n %err ⟨%ys, %c, %H, Hp, HS, #He, %Ht⟩
  iapply HΦ
  iexists ys, c
  iframe Hp HS He
  ipureintro
  exact ⟨⟨H.1, H.2.1, h _ _ _ H.2.1 H.2.2⟩, Ht⟩

/-- An `io.readerOk` reader with no condition on its calls keeps its buffer's tail. -/
theorem readerOkOut_of_readerOk (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) :
    readerOk ri (fun _ _ => True) S E ⊢ readerOkOut keepOut ri S E := by
  iintro #Hr
  unfold readerOkOut
  imodintro
  iintro %r %p %xs %Φ
  imodintro
  iintro ⟨HS, Hp⟩ HΦ
  iapply wp_reader_Read ri (fun _ _ => True) S E r p xs trivial $$ [HS Hp]
  · iframe Hr HS Hp
  inext
  iintro %n %err ⟨%ys, %H, Hp, HS, #He, %Ht⟩
  iapply HΦ
  iexists ys, _
  iframe Hp HS He
  ipureintro
  exact ⟨⟨H.1, H.2, rfl⟩, Ht⟩

/-- A reader keeping its buffer's tail is an `io.readerOk` reader, for any condition on its
calls. -/
theorem readerOk_of_readerOkOut (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF) :
    readerOkOut keepOut ri S E ⊢ readerOk ri Pre S E := by
  iintro #Hr
  unfold readerOk
  imodintro
  iintro %r %p %xs %Φ
  imodintro
  iintro ⟨-, HS, Hp⟩ HΦ
  unfold readerOkOut
  iapply Hr $$ %r %p %xs [HS Hp]
  · iframe
  inext
  iintro %n %err ⟨%ys, %c, %H, Hp, HS, #He, %Ht⟩
  iapply HΦ
  iexists ys
  have hc : c = ys ++ xs.drop ys.length := H.2.2
  subst hc
  iframe Hp HS He
  ipureintro
  exact ⟨⟨H.1, H.2.1⟩, Ht⟩

/-- What `io.ReadAtLeast(r, buf, min)` returns after delivering `ys` from `r` on, `buf` having
`m` bytes: with `m < min`, nothing and `ErrShortBuffer` (`sb`); else at least `min` bytes and
`nil`, or fewer and the reader's last error `e` (with its evidence `E (r ++ ys) e`), but
`ErrUnexpectedEOF` (`ueof`) in place of `EOF` (`eof`) when some bytes came first. -/
def readAtLeastRes (E : List w8 → GoInterface → IProp GF) (eof ueof sb : GoInterface)
    (r ys : List w8) (m : Nat) (min : Int) (err : GoInterface) : IProp GF :=
  iprop(⌜(m : Int) < min ∧ ys = [] ∧ err = sb⌝ ∨
    ⌜min ≤ m ∧ min ≤ ys.length ∧ err = interface.nil⌝ ∨
    ∃ e : GoInterface, ⌜min ≤ m ∧ (ys.length : Int) < min ∧ e ≠ interface.nil ∧
      (e = eof ∧ ys ≠ [] → err = ueof) ∧ (¬ (e = eof ∧ ys ≠ []) → err = e)⌝ ∗ □ E (r ++ ys) e)

instance readAtLeastRes_persistent (E : List w8 → GoInterface → IProp GF)
    (eof ueof sb : GoInterface) (r ys : List w8) (m : Nat) (min : Int) (err : GoInterface) :
    Persistent (readAtLeastRes E eof ueof sb r ys m min err) := by
  unfold readAtLeastRes; infer_instance

/-- What `io.ReadFull(r, buf)` returns after delivering `ys` from `r` on, `buf` having `m`
bytes: all `m` and `nil`, or fewer and the reader's last error `e` (with its evidence
`E (r ++ ys) e`), but `ErrUnexpectedEOF` (`ueof`) in place of `EOF` (`eof`) when some bytes came
first. -/
def readFullRes (E : List w8 → GoInterface → IProp GF) (eof ueof : GoInterface)
    (r ys : List w8) (m : Nat) (err : GoInterface) : IProp GF :=
  iprop(⌜ys.length = m ∧ err = interface.nil⌝ ∨
    ∃ e : GoInterface, ⌜ys.length < m ∧ e ≠ interface.nil ∧
      (e = eof ∧ ys ≠ [] → err = ueof) ∧ (¬ (e = eof ∧ ys ≠ []) → err = e)⌝ ∗ □ E (r ++ ys) e)

instance readFullRes_persistent (E : List w8 → GoInterface → IProp GF) (eof ueof : GoInterface)
    (r ys : List w8) (m : Nat) (err : GoInterface) :
    Persistent (readFullRes E eof ueof r ys m err) := by
  unfold readFullRes; infer_instance

/-- `ReadFull` is `ReadAtLeast` of all of `buf`. -/
theorem readFullRes_of_readAtLeastRes (E : List w8 → GoInterface → IProp GF)
    (eof ueof sb : GoInterface) (r ys : List w8) (m : Nat) (err : GoInterface)
    (hys : ys.length ≤ m) :
    readAtLeastRes E eof ueof sb r ys m (m : Int) err ⊢ readFullRes E eof ueof r ys m err := by
  unfold readAtLeastRes readFullRes
  iintro (%h | %h | ⟨%e, %h, #HE⟩)
  · exfalso; omega
  · ileft; ipureintro; exact ⟨by omega, h.2.2⟩
  · iright; iexists e; iframe HE; ipureintro
    exact ⟨by omega, h.2.2.1, h.2.2.2⟩

end defs

end io

end Perennial
