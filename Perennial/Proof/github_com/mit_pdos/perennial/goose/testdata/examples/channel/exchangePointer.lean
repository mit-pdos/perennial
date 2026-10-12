/-
The proof of `channel.exchangePointer`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.exchangePointer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.exchangePointer.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.exchangePointer.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#Hch, -, Hoc⟩
  imod start_handshake (V := Unit) ch (fun _ => iprop(x_ptr ↦ W64 1))
    iprop(y_ptr ↦ W64 2) γ $$ Hch Hoc with #H
  ipersist ch
  wp_apply wp_fork $$ [x]
  · wp_auto
    wp_apply wp_handshake_send (t := go.GoType.StructType []) γ ch () _ _ $$ [$H $x] as y
    itrivial
  wp_apply wp_handshake_receive (t := go.GoType.StructType []) γ ch _ _ $$ [$H $y] as %v x
  wp_end

end proof

end Perennial
