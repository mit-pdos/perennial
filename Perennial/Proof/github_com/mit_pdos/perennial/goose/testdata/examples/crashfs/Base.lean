/-
Shared definitions of the proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/crashfs`: its `isPkgInit` and the invariant
of the file `"f"`.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Base
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std fs_ext

namespace github_com.mit_pdos.perennial.goose.testdata.examples.crashfs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs :=
  build_get_is_pkg_init_wf

/-- The witness that the file is done. -/
abbrev fileDone (γ : GName) : IProp GF := dghostVar γ .discard ()

/-- The ghost state of the file's contents `c`: `""` (not done yet), with the ghost
variable `γ`; or `"done"`, with `γ` discarded, so that `fileDone γ`, held by
whoever saw the file done, rules out the first case. -/
abbrev fileState (γ : GName) (c : GoString) : IProp GF :=
  iprop((⌜c = go!""⌝ ∗ dghostVar γ (.own 1) ()) ∨ (⌜c = go!"done"⌝ ∗ fileDone γ))

/-- The invariant of the file `"f"`, under the files' ghost state `hF`. It always
owns the file, so that a crash does not lose it. -/
abbrev fileInv (hF : FsGS GF) (γ : GName) : IProp GF :=
  iprop(∃ c : GoString, fsPointsto hF go!"f" (.own 1) c ∗ fileState γ c)

open Iris.ProofMode in
/-- A reader learns that the file is `""` or `"done"`, and if `"done"`, the witness. -/
theorem fileState_read (γ : GName) (c : GoString) :
    fileState (GF := GF) γ c ⊢
      ⌜c = go!"" ∨ c = go!"done"⌝ ∗ □ (⌜c = go!"done"⌝ -∗ fileDone γ) ∗ fileState γ c := by
  unfold fileState
  iintro (⟨%Hc, Hown⟩ | ⟨%Hc, #Hd⟩) <;> subst Hc
  · isplitr
    · ipureintro; exact .inl rfl
    isplitr
    · iintro !> %Hc
      cases Hc
    ileft; iframe Hown; ipureintro; rfl
  · isplitr
    · ipureintro; exact .inr rfl
    isplitr
    · iintro !> _
      iexact Hd
    iright; iframe Hd; ipureintro; rfl

open Iris.ProofMode in
/-- The writer of `"done"` gets the witness. -/
theorem fileState_write (γ : GName) (c : GoString) :
    fileState (GF := GF) γ c ==∗ fileDone γ ∗ fileState γ go!"done" := by
  unfold fileState
  iintro (⟨%_, Hown⟩ | ⟨%_, #Hd⟩)
  all_goals try imod dghostVar_persist γ 1 () $$ Hown with #Hd
  all_goals
    imodintro
    isplitr
    · iexact Hd
    iright
    isplitr
    · ipureintro; rfl
    iexact Hd

open Iris.ProofMode in
/-- With the witness, the file is done. -/
theorem fileState_done (γ : GName) (c : GoString) :
    ⊢@{IProp GF} fileDone γ -∗ fileState γ c -∗ ⌜c = go!"done"⌝ ∗ fileState γ c := by
  unfold fileState
  iintro #Hd (⟨%_, Hown⟩ | ⟨%Hc, _⟩)
  · icases dghostVar_valid_2 γ () (.own 1) () .discard $$ Hown Hd with %H
    exact absurd (DFrac.valid_own_op_discard.mp H.1) (by simp)
  · subst Hc
    isplitr
    · ipureintro; rfl
    iright; iframe Hd; ipureintro; rfl

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.crashfs

end Perennial
