/-
Common setup for the goose semantics tests (`TestFunOk` and the
`semantics_auto` tactic).

The `semantics` package imports `github.com/goose-lang/primitive/disk`, so the
FFI is the disk FFI (via `DiskPrelude`): the generated
  `semantics.Assumptions` is stated for `disk_op`, and the sections below do not
bind `FfiSyntax`/`FfiModel`.
-/
import Perennial.Proof.DiskPrelude
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics
import Perennial.Proof.sync_proof.base
import Perennial.Proof.encoding.binary
import Perennial.Proof.github_com.goose_lang.primitive
import Perennial.Proof.github_com.goose_lang.primitive.disk

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.semantics :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.semantics :=
  build_get_is_pkg_init_wf

/-- A semantics test function `name` returns `true`. -/
def TestFunOk (name : GoString) : Prop :=
  ∀ Φ : val → IProp GF, ⊢ Φ #true -∗ WP (App (Val (@! name)) (Val #())) {{ Φ }}

omit go_gctx in
/-- `Φ v ⊢ Φ w` when `v = w`. -/
theorem exact_eq {Φ : val → IProp GF} {v w : val} (h : v = w) : Φ v ⊢ Φ w := h ▸ .rfl

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

/-- Step through a function or method call. -/
macro "wp_call_auto" : tactic =>
  `(tactic| first | (wp_func_call; wp_call) | (wp_method_call; wp_call) | wp_call)

/-- Repeatedly step calls, pure steps and anonymous allocations (`wp_alloc_anon`). -/
macro "steps" : tactic =>
  `(tactic| repeat (first | wp_call_auto | wp_auto | wp_alloc_anon))

set_option hygiene false in
/-- Start a `TestFunOk` proof, step through the
function and try to close the goal `Φ #b` with `HΦ : Φ #true`. -/
macro "semantics_auto" : tactic => `(tactic| (
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  steps
  try (first
    | iexact HΦ
    | (iapply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.exact_eq ?_ $$ HΦ
       all_goals first | rfl | (simp; done) | decide))))

end Perennial
