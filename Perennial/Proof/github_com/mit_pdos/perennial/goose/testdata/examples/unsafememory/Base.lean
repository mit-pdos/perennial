/-
Common setup for the proofs of the `unsafememory` examples (`goose/testdata/examples/unsafememory`,
the acceptance tests of `docs/design/unsafe-memory.md`): the package's `isPkgInit` instances,
`TestFunOk` (each target returns `true`), and the `unsafememory_auto` tactic.
-/
module

public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory
public import Perennial.Proof.bytes.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.time.Base
public import Perennial.Golang.Theory.Plain
public import Perennial.Proof.«unsafe».Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory :=
  build_get_is_pkg_init_wf

/-- A target function `name` returns `true`. -/
def TestFunOk (name : GoString) : Prop :=
  ∀ Φ : val → IProp GF, ⊢ Φ #true -∗ WP (App (Val (@! name)) (Val #())) {{ Φ }}

omit go_gctx in
/-- `Φ v ⊢ Φ w` when `v = w`. -/
theorem exact_eq {Φ : val → IProp GF} {v w : val} (h : v = w) : Φ v ⊢ Φ w := h ▸ .rfl

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

/-- Repeatedly step calls, pure steps and anonymous allocations. -/
macro "unsafememory_steps" : tactic =>
  `(tactic| repeat (first
    | (wp_func_call; wp_call)
    | (wp_method_call; wp_call)
    | wp_call
    | wp_auto
    | wp_alloc_anon))

set_option hygiene false in
/-- Start a `TestFunOk` proof, step through the function and try to close `Φ #b` with
`HΦ : Φ #true`. -/
macro "unsafememory_auto" : tactic => `(tactic| (
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  unsafememory_steps
  try (first
    | iexact HΦ
    | (iapply github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.exact_eq ?_ $$ HΦ
       all_goals first | rfl | (simp; done) | decide))))

end Perennial
