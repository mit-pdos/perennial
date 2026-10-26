/-
The proof of `channel.HelloWorldWithTimeout`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldWithTimeout
public import Perennial.Spec.time.Sleep
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldCancellable

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldWithTimeout.wp_proof
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG))
    (wp_HelloWorldCancellable :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldCancellable.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldWithTimeout.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#Hchan, -, Hoc⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(errMsg_ptr ↦□ go!"operation timed out") γ ch
    $$ Hchan Hoc with Hown
  ihave #Hdone_bc := ownBroadcastChan_Unknown _ _ _ _ $$ Hown
  ipersist done
  wp_apply wp_fork $$ [Hown errMsg]
  · wp_auto
    wp_apply wp_Sleep
    ipersist errMsg
    wp_apply wp_broadcast_chan_close (ty := go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType []))
      ch γ _ $$ [$Hown $errMsg] as -
    itrivial
  wp_apply wp_HelloWorldCancellable $$ [$Hdone_bc] as %result %Hres
  iapply HΦ
  ipureintro
  rcases Hres with h | h <;> simp [h]

end proof

end Perennial
