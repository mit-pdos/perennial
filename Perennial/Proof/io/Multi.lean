/-
Shared definitions of the proofs of `io.MultiReader` (`io/multi.go`): the readers it
concatenates, each with its contract (`io.ReaderC`, read by `io.readerOkOut`), and the state
(`io.mrState`) and errors (`io.mrErr`) of the `*multiReader` it returns, read as the
concatenation of their streams.
-/
module

public import Perennial.Proof.io.Reader

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

variable (GF) in
/-- **One reader of a `MultiReader`**: its value (a non-nil `io.Reader`) and the state `S` and
errors `E` of its contract (`io.readerOkOut`). -/
structure ReaderC where
  ri : GoInterfaceOk
  S : List w8 → IProp GF
  E : List w8 → GoInterface → IProp GF

/-- The reader as an `io.Reader` value. -/
abbrev ReaderC.iface (c : ReaderC GF) : GoInterface := interface.ok c.ri

/-- The readers that have not returned `EOF` yet, the first having delivered `cur`, the others
nothing. -/
def mrCur : List (ReaderC GF) → List w8 → IProp GF
  | [], cur => iprop(⌜cur = []⌝)
  | c :: rest, cur => iprop(c.S cur ∗ [∗list] c' ∈ rest, c'.S [])

theorem mrCur_nil (cur : List w8) : mrCur (GF := GF) [] cur = iprop(⌜cur = []⌝) := rfl

theorem mrCur_cons (c : ReaderC GF) (rest : List (ReaderC GF)) (cur : List w8) :
    mrCur (GF := GF) (c :: rest) cur = iprop(c.S cur ∗ [∗list] c' ∈ rest, c'.S []) := rfl

/-- Readers none of which has delivered anything. -/
theorem mrCur_init (cs : List (ReaderC GF)) :
    ([∗list] c ∈ cs, c.S []) ⊢ mrCur cs [] := by
  cases cs with
  | nil => iintro -; unfold mrCur; ipureintro; rfl
  | cons c rest =>
    iintro H
    unfold mrCur
    iapply BigSepL.bigSepL_cons.1 $$ H

/-- The readers that have returned `EOF`, each `(c, d)` with what it delivered `d`, and its
evidence `c.E d eof` (persistent). -/
def mrDone (done : List (ReaderC GF × List w8)) (eof : GoInterface) : IProp GF :=
  iprop(□ ∀ d, ⌜d ∈ done⌝ -∗ d.1.E d.2 eof)

instance mrDone_persistent (done : List (ReaderC GF × List w8)) (eof : GoInterface) :
    Persistent (mrDone done eof) := by
  unfold mrDone; infer_instance

theorem mrDone_nil (eof : GoInterface) : ⊢ mrDone (GF := GF) [] eof := by
  unfold mrDone
  imodintro
  iintro %d %h
  exact absurd h List.not_mem_nil

theorem mrDone_snoc (done : List (ReaderC GF × List w8)) (c : ReaderC GF) (d : List w8)
    (eof : GoInterface) :
    mrDone done eof ∗ □ c.E d eof ⊢ mrDone (done ++ [(c, d)]) eof := by
  iintro ⟨#Hd, #He⟩
  unfold mrDone
  imodintro
  iintro %x %hx
  rcases List.mem_append.1 hx with h | h
  · iapply Hd $$ %x %h
  · simp only [List.mem_singleton] at h
    subst h
    iexact He

/-- **The state of a `*multiReader` `l` of the readers `cs`, having delivered `r`**: the readers
of `done` have returned `EOF` (`mrDone`), and the rest, `rem`, are still in its slice `readers`;
the first of them has delivered `cur` (`mrCur`), so `r` is what the done readers delivered,
then `cur`. `eof` is `io.EOF`'s value. -/
def mrState (l : Loc) (cs : List (ReaderC GF)) (eof : GoInterface) (r : List w8) : IProp GF :=
  iprop(∃ (done : List (ReaderC GF × List w8)) (rem : List (ReaderC GF)) (sl : GoSlice)
      (cur : List w8),
    ⌜cs = done.map Prod.fst ++ rem ∧ r = (done.map Prod.snd).flatten ++ cur⌝ ∗
    l ↦ ({ readers' := sl } : multiReader) ∗ sl ↦* rem.map ReaderC.iface ∗
    mrDone done eof ∗ mrCur rem cur)

/-- **What an error of a `*multiReader` of `cs`, having delivered `r`, says** (persistent): it is
an error `e` other than `EOF` (`eof`) that the current reader `c` returned, with its evidence, or
`EOF` once every reader has returned `EOF` (each with its evidence). -/
def mrErr (cs : List (ReaderC GF)) (eof : GoInterface) (r : List w8) (e : GoInterface) :
    IProp GF :=
  iprop((∃ (done : List (ReaderC GF × List w8)) (c : ReaderC GF) (rem : List (ReaderC GF))
      (cur : List w8),
      ⌜e ≠ eof ∧ cs = done.map Prod.fst ++ c :: rem ∧ r = (done.map Prod.snd).flatten ++ cur⌝ ∗
      mrDone done eof ∗ □ c.E cur e) ∨
    (∃ done : List (ReaderC GF × List w8),
      ⌜e = eof ∧ cs = done.map Prod.fst ∧ r = (done.map Prod.snd).flatten⌝ ∗ mrDone done eof))

instance mrErr_persistent (cs : List (ReaderC GF)) (eof : GoInterface) (r : List w8)
    (e : GoInterface) : Persistent (mrErr cs eof r e) := by
  unfold mrErr; infer_instance

end defs

end io

end Perennial
