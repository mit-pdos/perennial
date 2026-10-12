/-
The proof of `channel.BroadcastExample`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.BroadcastExample

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.BroadcastExample.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.BroadcastExample.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_apply chan.wp_make1 (V := Unit) as %done_ch %γdone ⟨#Hdone_ch, -, Hdone_own⟩
  wp_apply chan.wp_make1 (V := w64) as %result1_ch %γr1 ⟨#Hr1_ch, -, Hr1_own⟩
  wp_apply chan.wp_make1 (V := w64) as %result2_ch %γr2 ⟨#Hr2_ch, -, Hr2_own⟩
  imod start_bag (fun (v : w64) => iprop(⌜v = W64 6⌝)) _ result1_ch γr1 trivial $$ Hr1_ch Hr1_own
    with #Hbag1
  imod start_bag (fun (v : w64) => iprop(⌜v = W64 10⌝)) _ result2_ch γr2 trivial $$ Hr2_ch Hr2_own
    with #Hbag2
  imod alloc_broadcast_chan (E := ⊤) iprop(sharedValue_ptr ↦□ W64 2) γdone done_ch
    $$ Hdone_ch Hdone_own with Hown_done
  ihave #Hdone_bc := ownBroadcastChan_Unknown _ _ _ _ $$ Hown_done
  ipersist done
  ipersist result1
  ipersist result2
  wp_apply wp_fork $$ []
  · wp_auto
    wp_apply_core chan.wp_receive (V := Unit) done_ch γdone $$ Hdone_ch
    iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone_bc
    iintro ⟨#HShared, -⟩
    wp_auto
    wp_apply wp_bag_send γr1 result1_ch _ _ $$ [$Hbag1]
    · ipureintro; decide
    itrivial
  wp_apply wp_fork $$ []
  · wp_auto
    wp_apply_core chan.wp_receive (V := Unit) done_ch γdone $$ Hdone_ch
    iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone_bc
    iintro ⟨#HShared, -⟩
    wp_auto
    wp_apply wp_bag_send γr2 result2_ch _ _ $$ [$Hbag2]
    · ipureintro; decide
    itrivial
  ipersist sharedValue
  wp_apply wp_broadcast_chan_close (ty := go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType []))
    done_ch γdone _ $$ [$Hown_done $sharedValue] as -
  wp_apply wp_bag_receive γr1 result1_ch _ $$ Hbag1 as %v1 %Hv1
  subst Hv1
  wp_apply wp_bag_receive γr2 result2_ch _ $$ Hbag2 as %v2 %Hv2
  subst Hv2
  wp_auto
  wp_end

end proof

end Perennial
