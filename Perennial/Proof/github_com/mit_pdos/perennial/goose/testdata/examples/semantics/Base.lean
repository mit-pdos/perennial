/-
Common setup for the goose semantics tests: the package's `isPkgInit` instances,
`TestFunOk`, the `semantics_auto` tactic, and helper lemmas (`exact_eq`,
`w64_pointsto_excl`).

The `semantics` package imports `github.com/goose-lang/primitive/disk`, so the
FFI is the disk FFI (via `DiskPrelude`): the generated
  `semantics.Assumptions` is stated for `disk_op`, and the sections below do not
bind `FfiSyntax`/`FfiModel`.

`wp_testAllocateDistinct` (`allocator.go`) is not stated (TODO: no map alloc?):
the map literal `map[uint64]unit{}` steps to a raw `AllocOp` of `map_empty`,
for which there is no spec. Nothing to state here yet.
-/
module

public import Perennial.Proof.DiskPrelude
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics
public import Perennial.Proof.sync.Base
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Perennial.Proof.github_com.goose_lang.primitive.disk.Base

@[expose] public section

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

/-- Two full points-tos for the same `w64` location are contradictory. -/
theorem w64_pointsto_excl (l : Loc) (v w : w64) :
    (typedPointsto l v (DFrac.own 1) : IProp GF) ∗ typedPointsto l w (DFrac.own 1) ⊢ False :=
  word_pointsto_excl l v w

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
