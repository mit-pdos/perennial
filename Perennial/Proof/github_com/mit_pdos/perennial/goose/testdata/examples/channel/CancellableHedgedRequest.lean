/-
The proof of `channel.CancellableHedgedRequest`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.CancellableHedgedRequest
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.GetPrimary
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.GetSecondary
public import Perennial.Spec.time.After

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.CancellableHedgedRequest.wp_proof
    (wp_GetPrimary :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.GetPrimary.spec
        (GF := GF) (hG := hG))
    (wp_GetSecondary :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.GetSecondary.spec
        (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.CancellableHedgedRequest.spec
      (GF := GF) (hG := hG) := fun query hedgeThreshold errStr_ptr' done_ch γdone => by
  wp_start as ⟨#Hdone_bc, HerrStr⟩
  ihave #Hdone_chan := ownBroadcastChan_is_chan _ _ _ _ $$ Hdone_bc
  wp_pures
  wp_alloc done_ptr as done
  wp_pures
  wp_alloc errStr_ptr as errStr
  wp_auto
  wp_apply chan.wp_make2 (V := Result) $$ [] as %c %γc ⟨#Hc_chan, -, Hc_own⟩
  · ipureintro; decide
  imod start_bag (fun (v : Result) => iprop(⌜v = Result.mk (query ++ go!"_primary.html") true ∨
      v = Result.mk (query ++ go!"_secondary.html") false⌝)) _ c γc trivial $$ Hc_chan Hc_own
    with #Hch
  ipersist query
  ipersist c
  -- the primary request is always launched immediately
  wp_apply wp_fork $$ []
  · wp_auto
    wp_apply wp_GetPrimary
    wp_apply wp_bag_send γc c _ _ $$ [$Hch]
    · ipureintro; exact .inl rfl
    itrivial
  -- `time.After` gives a channel that fires after the hedge threshold
  wp_apply +noauto wp_After
  iintro %hedge_ch %γhedge #Hhedge
  wp_auto_lc 4
  -- first select: result on `c` | hedge threshold fires | `done` closes
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the primary responded before the hedge threshold
    dsimp only [chan.blockingClausePre]
    iexists Result, inferInstance, inferInstance, inferInstance, inferInstance, c, γc
    isplitr
    · ipureintro; rfl
    iframe Hc_chan
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hch
    inext
    iintro %v %Hres
    wp_auto
    rcases Hres with rfl | rfl
    · iapply HΦ; ileft; ipureintro; exact .inl ⟨rfl, rfl⟩
    · iapply HΦ; ileft; ipureintro; exact .inr ⟨rfl, rfl⟩
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the hedge threshold fired: launch the secondary and wait again
    dsimp only [chan.blockingClausePre]
    ihave #Hhedge_chan := is_bag_is_chan _ _ _ $$ Hhedge
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, hedge_ch, γhedge
    isplitr
    · ipureintro; rfl
    iframe Hhedge_chan
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hhedge
    inext
    iintro %v -
    wp_auto
    wp_apply wp_fork $$ []
    · wp_auto
      wp_apply wp_GetSecondary
      wp_apply wp_bag_send γc c _ _ $$ [$Hch]
      · ipureintro; exact .inr rfl
      itrivial
    -- second select: result on `c` | `done` closes
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      iexists Result, inferInstance, inferInstance, inferInstance, inferInstance, c, γc
      isplitr
      · ipureintro; rfl
      iframe Hc_chan
      iapply bag_recv_au $$ [$Hlc3 $Hlc4] Hch
      inext
      iintro %v %Hres
      wp_auto
      rcases Hres with rfl | rfl
      · iapply HΦ; ileft; ipureintro; exact .inl ⟨rfl, rfl⟩
      · iapply HΦ; ileft; ipureintro; exact .inr ⟨rfl, rfl⟩
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, done_ch, γdone
      isplitr
      · ipureintro; rfl
      iframe Hdone_chan
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone_bc
      iintro ⟨-, -⟩
      wp_auto
      iapply HΦ
      iright
      iframe
      ipureintro; exact ⟨rfl, rfl⟩
    · iapply BigAndL.bigAndL_nil.2
      itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `done` was closed first
    dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, done_ch, γdone
    isplitr
    · ipureintro; rfl
    iframe Hdone_chan
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone_bc
    iintro ⟨-, -⟩
    wp_auto
    iapply HΦ
    iright
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end Perennial
