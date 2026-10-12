/-
`channel.CancellableHedgedRequest`'s spec (hedged requests, cancellation).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.channel.CancellableHedgedRequest.spec : Prop :=
  ∀ (query : GoString) (hedgeThreshold : time.Duration) (errStr_ptr' : Loc) (done_ch : GoChan)
    (γdone : ChanNames),
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        ownBroadcastChan done_ch γdone iprop(True) .Unknown ∗
        errStr_ptr' ↦ go!"" }}
      (App (App (App (App (Val (@! CancellableHedgedRequest)) (Val #query)) (Val #hedgeThreshold))
        (Val #errStr_ptr')) (Val #done_ch))
    {{ (v : GoString) (b : Bool), RET #(Result.mk v b);
        -- primary won, or the hedged request won
        iprop(⌜(v = query ++ go!"_primary.html" ∧ b = true) ∨
          (v = query ++ go!"_secondary.html" ∧ b = false)⌝) ∨
        -- `done` was closed before any result arrived: the caller wrote "cancelled"
        -- into `errStr_ptr'` and the zero `Result` is returned
        iprop(errStr_ptr' ↦ go!"cancelled" ∗ ⌜v = go!"" ∧ b = false⌝) }}

end spec

end Perennial
