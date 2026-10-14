/-
The proof of `channel/workq`'s `initialize'`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.initialize
public import Perennial.Spec.sync.atomic.initialize
public import Perennial.Spec.strings.initialize

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.initialize'.wp_proof
    (wp_atomic_initialize : sync.atomic.initialize'.spec (GF := GF) (hG := hG))
    (wp_strings_initialize : strings.initialize'.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.initialize'.spec
      (GF := GF) (hG := hG) := fun get_is_pkg_init Hinit => by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_atomic_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hatomic⟩
  wp_apply wp_strings_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hstrings⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
