/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/semantics_proof/semantics_init.v`:
common setup for the goose semantics tests (`test_fun_ok` and the
`semantics_auto` tactic).

Differences from Rocq:
* The `semantics` package imports `github.com/goose-lang/primitive/disk`, so (as
  in Rocq, via `disk_prelude`) the FFI is the disk FFI: the generated
  `semantics.Assumptions` is stated for `disk_op`, and the sections below do not
  bind `ffi_syntax`/`ffi_model`.
* The `IsPkgInit`/`GetIsPkgInitWf` instances of `semantics` are not defined yet
  (TODO(port)): `define_is_pkg_init` needs the instances of all imported
  packages, and `encoding/binary` and `primitive/disk` have no proofs yet.
  `test_fun_ok` does not mention `is_pkg_init`, so no test needs them.
-/
import Perennial.Proof.DiskPrelude
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.TacticWorkarounds
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]

/-- A semantics test function `name` returns `true`. -/
def test_fun_ok (name : go_string) : Prop :=
  ∀ Φ : val → IProp GF, ⊢ Φ #true -∗ WP (App (Val (@! name)) (Val #())) {{ Φ }}

omit go_gctx in
/-- Rocq `iExactEq`: `Φ v ⊢ Φ w` when `v = w`. -/
theorem exact_eq {Φ : val → IProp GF} {v w : val} (h : v = w) : Φ v ⊢ Φ w := h ▸ .rfl

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

/-- Rocq `wp_call_auto`. -/
macro "wp_call_auto" : tactic =>
  `(tactic| first | (wp_func_call; wp_call) | (wp_method_call; wp_call) | wp_call)

/-- Rocq `steps` (`wp_alloc_anon` is Rocq's `wp_alloc x as "?"`). -/
macro "steps" : tactic =>
  `(tactic| repeat (first | wp_call_auto | wp_auto | wp_alloc_anon))

set_option hygiene false in
/-- Rocq `semantics_auto`: start a `test_fun_ok` proof, step through the
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
