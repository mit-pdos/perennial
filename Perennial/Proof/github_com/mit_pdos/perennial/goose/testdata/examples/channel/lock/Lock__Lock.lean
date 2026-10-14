/-
The proof of `lock.Lock.Lock`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock__Lock

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock.Lock.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.lock.Lock.Lock.spec
      (GF := GF) (hG := hG) := fun γ l R => by
  wp_start as #Hl
  unfold isLock
  wp_auto
  wp_apply wp_lock_channel_lock (t := go.GoType.StructType []) γ l.ch' () R $$ Hl as HR
  iapply HΦ $$ HR

end proof

end Perennial
