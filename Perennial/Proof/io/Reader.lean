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
