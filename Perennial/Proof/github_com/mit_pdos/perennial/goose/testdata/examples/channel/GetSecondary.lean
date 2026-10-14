/-
The proof of `channel.GetSecondary`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.GetSecondary

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.GetSecondary.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.GetSecondary.spec
      (GF := GF) (hG := hG) := fun q => by
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
