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

/-- The invariant of the file `"f"`: it holds `""` (not done yet), and the invariant
owns the ghost variable `γ`; or it holds `"done"`, and `γ` is discarded, so
that its persistent `dghostVar γ .discard ()`, held by whoever saw it done, rules
out the first case. The invariant always owns the file, so that a crash does
not lose it. -/
def fileInv (γ : GName) : IProp GF :=
  iprop(∃ c : GoString, go!"f" fs↦ c ∗
    ((⌜c = go!""⌝ ∗ dghostVar γ (.own 1) ()) ∨ (⌜c = go!"done"⌝ ∗ dghostVar γ .discard ())))

open Iris.ProofMode in
/-- Either state of the invariant gives the witness that the file is done, at the
cost of the first state's ghost variable. -/
theorem fileInv_witness (γ : GName) (c : GoString) :
    ⊢@{IProp GF} ((⌜c = go!""⌝ ∗ dghostVar γ (.own 1) ()) ∨
        (⌜c = go!"done"⌝ ∗ dghostVar γ .discard ())) ==∗ dghostVar γ .discard () := by
  iintro (⟨%_, Hown⟩ | ⟨%_, #Hd⟩)
  · iapply dghostVar_persist γ 1 () $$ Hown
  · imodintro; iexact Hd

open Iris.ProofMode in
/-- With the witness, the file is done. -/
theorem fileInv_done (γ : GName) (c : GoString) :
    ⊢@{IProp GF} dghostVar γ .discard () -∗ ((⌜c = go!""⌝ ∗ dghostVar γ (.own 1) ()) ∨
        (⌜c = go!"done"⌝ ∗ dghostVar γ .discard ())) -∗
      ⌜c = go!"done"⌝ ∗ (⌜c = go!"done"⌝ ∗ dghostVar γ .discard ()) := by
  iintro #Hd (⟨%_, Hown⟩ | ⟨%Hc, Hd'⟩)
  · icases dghostVar_valid_2 γ () (.own 1) () .discard $$ Hown Hd with %H
    exact absurd (DFrac.valid_own_op_discard.mp H.1) (by simp)
  · iframe Hd'; isplitl [] <;> ipureintro <;> exact Hc

open Iris.ProofMode in
/-- What a reader of the invariant learns: the file is `""` or `"done"`, and if
it is `"done"`, the witness. -/
theorem fileInv_cases (γ : GName) (c : GoString) :
    ⊢@{IProp GF} ((⌜c = go!""⌝ ∗ dghostVar γ (.own 1) ()) ∨
        (⌜c = go!"done"⌝ ∗ dghostVar γ .discard ())) -∗
      ⌜c = go!"" ∨ c = go!"done"⌝ ∗ □ (⌜c = go!"done"⌝ -∗ dghostVar γ .discard ()) ∗
      ((⌜c = go!""⌝ ∗ dghostVar γ (.own 1) ()) ∨ (⌜c = go!"done"⌝ ∗ dghostVar γ .discard ())) := by
  iintro (⟨%Hc, Hown⟩ | ⟨%Hc, #Hd⟩)
  · isplitr
    · ipureintro; exact .inl Hc
    isplitr
    · iintro !> %Hc'
      subst Hc; cases Hc'
    ileft; iframe Hown; ipureintro; exact Hc
  · isplitr
    · ipureintro; exact .inr Hc
    isplitr
    · iintro !> _; iexact Hd
    iright; iframe Hd; ipureintro; exact Hc

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.crashfs

end Perennial
