/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel.v`:
hedged requests, hello-world futures, cancellation, joins, pointer exchange and
broadcast examples, using the channel idioms (bag, handshake, broadcast, future).
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel_examples_init
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Golang.Theory.Chan.Idioms.Handshake
import Perennial.Golang.Theory.Chan.Idioms.Broadcast
import Perennial.Golang.Theory.Chan.Idioms.Future
import Perennial.Proof.time

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

instance Result.countable [FfiSyntax] : Pos.Countable Result :=
  .ofInjective (fun r => Pos.Countable.encode (r.value', r.primary_won'))
    (by rintro ⟨a, b⟩ ⟨c, d⟩ h; have h := Pos.encode_inj h; simp_all)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

/-! ### Hedged requests -/

theorem wp_GetPrimary (q : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! GetPrimary)) (Val #q))
    {{ RET #(q ++ go!"_primary.html"); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_GetSecondary (q : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! GetSecondary)) (Val #q))
    {{ RET #(q ++ go!"_secondary.html"); True }} := by
  wp_start
  wp_auto
  wp_end

/-! ### Hello world -/

theorem wp_sys_hello_world :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! sys_hello_world)) (Val #()))
    {{ RET #(go!"Hello, World!"); True }} := by
  wp_start
  wp_end

theorem wp_HelloWorldAsync :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! HelloWorldAsync)) (Val #()))
    {{ (ch : Loc) (γfut : ChanNames), RET #ch;
        isChan ch γfut GoString ∗
        isChanBag γfut ch (fun (v : GoString) => iprop(⌜v = go!"Hello, World!"⌝)) }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := GoString) $$ [] as %ch %γ ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  imod start_bag (fun (v : GoString) => iprop(⌜v = go!"Hello, World!"⌝)) _ ch γ trivial $$ Hch Hoc
    with #Hbag
  ipersist ch
  wp_apply wp_fork $$ []
  · wp_auto
    wp_apply wp_sys_hello_world
    wp_apply wp_bag_send γ ch _ _ $$ [$Hbag]
    · ipureintro; rfl
    itrivial
  iapply HΦ
  iframe #

theorem wp_HelloWorldSync :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! HelloWorldSync)) (Val #()))
    {{ RET #(go!"Hello, World!"); True }} := by
  wp_start
  wp_apply wp_HelloWorldAsync as %ch %γ ⟨#Hch, #Hbag⟩
  wp_apply wp_bag_receive γ ch _ $$ Hbag as %v %Hv
  subst Hv
  wp_end

/-! ### Joins -/

theorem wp_simple_join :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! simple_join)) (Val #()))
    {{ RET #(go!"Hello, World!"); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := Unit) $$ [] as %ch %γ ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  imod start_future (V := Unit) ch γ _ (.inr rfl) $$ Hch Hoc
    with ⟨%γfut, #Hfut, HAwait⟩
  imod future_alloc_promise (V := Unit) γfut ch
    (fun _ => iprop(message_ptr ↦ go!"Hello, World!")) [] $$ Hfut HAwait with ⟨Hpromise, HAwait⟩
  ipersist ch
  wp_apply wp_fork $$ [Hpromise message]
  · wp_auto
    wp_apply wp_future_fulfill (t := go.GoType.StructType []) γfut ch () $$ [$Hfut Hpromise message]
    · unfold Fulfilled; iexists _; iframe; iassumption
    itrivial
  wp_apply wp_future_await (t := go.GoType.StructType []) γfut ch _ $$ [$Hfut $HAwait]
    as %v %P %pre %post ⟨%Hsplit, HP, -⟩
  rcases pre with _ | ⟨_, pre⟩
  · simp only [List.nil_append, List.cons.injEq] at Hsplit
    obtain ⟨rfl, -⟩ := Hsplit
    wp_auto
    wp_end
  · simp at Hsplit

theorem wp_simple_multi_join :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! simple_multi_join)) (Val #()))
    {{ RET #(go!"Hello World"); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := Unit) $$ [] as %ch %γ ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  imod start_future (V := Unit) ch γ _ (.inr rfl) $$ Hch Hoc
    with ⟨%γfut, #Hfut, HAwait⟩
  imod future_alloc_promise (V := Unit) γfut ch
    (fun _ => iprop(hello_ptr ↦ go!"Hello")) [] $$ Hfut HAwait with ⟨Hpromise1, HAwait⟩
  imod future_alloc_promise (V := Unit) γfut ch
    (fun _ => iprop(world_ptr ↦ go!"World")) _ $$ Hfut HAwait with ⟨Hpromise2, HAwait⟩
  ipersist ch
  wp_apply wp_fork $$ [Hpromise1 hello]
  · wp_auto
    wp_apply wp_future_fulfill (t := go.GoType.StructType []) γfut ch () $$ [$Hfut Hpromise1 hello]
    · unfold Fulfilled; iexists _; iframe; iassumption
    itrivial
  wp_apply wp_fork $$ [Hpromise2 world]
  · wp_auto
    wp_apply wp_future_fulfill (t := go.GoType.StructType []) γfut ch () $$ [$Hfut Hpromise2 world]
    · unfold Fulfilled; iexists _; iframe; iassumption
    itrivial
  wp_apply wp_future_await (t := go.GoType.StructType []) γfut ch _ $$ [$Hfut $HAwait]
    as %v1 %P1 %pre1 %post1 ⟨%Hsplit1, HP1, HAwait⟩
  -- which contract was fulfilled first
  rcases pre1 with _ | ⟨_, _ | ⟨_, pre1⟩⟩
  · simp only [List.nil_append] at Hsplit1
    obtain ⟨rfl, rfl⟩ := Hsplit1
    wp_apply wp_future_await (t := go.GoType.StructType []) γfut ch _ $$ [$Hfut $HAwait]
      as %v2 %P2 %pre2 %post2 ⟨%Hsplit2, HP2, -⟩
    rcases pre2 with _ | ⟨_, pre2⟩
    · simp only [List.nil_append] at Hsplit2
      obtain ⟨rfl, -⟩ := Hsplit2
      wp_auto
      simp only [List.cons_append, List.nil_append]
      wp_end
    · simp at Hsplit2
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at Hsplit1
    obtain ⟨rfl, rfl, rfl⟩ := Hsplit1
    wp_apply wp_future_await (t := go.GoType.StructType []) γfut ch _ $$ [$Hfut $HAwait]
      as %v2 %P2 %pre2 %post2 ⟨%Hsplit2, HP2, -⟩
    rcases pre2 with _ | ⟨_, pre2⟩
    · simp only [List.nil_append] at Hsplit2
      obtain ⟨rfl, -⟩ := Hsplit2
      wp_auto
      simp only [List.cons_append, List.nil_append]
      wp_end
    · simp at Hsplit2
  · simp at Hsplit1

/-! ### Exchanging pointers through a handshake -/

theorem wp_exchangePointer :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! exchangePointer)) (Val #()))
    {{ RET #(); True }} := by
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

/-! ### Broadcast -/

theorem wp_BroadcastExample :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! BroadcastExample)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
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

/-! ### Cancellation -/

theorem wp_HelloWorldCancellable (done_ch : chan.t) (err_ptr1 : Loc) (err_msg : GoString)
    (γdone : ChanNames) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        ownBroadcastChan done_ch γdone iprop(err_ptr1 ↦□ err_msg) .Unknown }}
      (App (App (Val (@! HelloWorldCancellable)) (Val #done_ch)) (Val #err_ptr1))
    {{ (result : GoString), RET #result;
        ⌜result = err_msg ∨ result = go!"Hello, World!"⌝ }} := by
  wp_start as #Hdone_bc
  ihave #Hdone_chan := ownBroadcastChan_is_chan _ _ _ _ $$ Hdone_bc
  wp_pures
  wp_alloc l as Hl
  wp_pures
  wp_alloc d as Hd
  wp_auto
  wp_apply +noauto wp_HelloWorldAsync
  iintro %ch %γfut ⟨#Hch, #Hfut⟩
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, ch, γfut
    isplitr
    · ipureintro; rfl
    iframe Hch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hfut
    inext
    iintro %v %Hv
    subst Hv
    wp_auto
    iapply HΦ
    ipureintro; exact .inr rfl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, done_ch, γdone
    isplitr
    · ipureintro; rfl
    iframe Hdone_chan
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone_bc
    iintro ⟨#Herr, -⟩
    wp_auto
    iapply HΦ
    ipureintro; exact .inl rfl
  · iapply BigAndL.bigAndL_nil.2
    itrivial

theorem wp_HelloWorldWithTimeout :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! HelloWorldWithTimeout)) (Val #()))
    {{ (result : GoString), RET #result;
        ⌜result = go!"Hello, World!" ∨ result = go!"operation timed out"⌝ }} := by
  wp_start
  wp_pures
  wp_alloc done_ptr as done
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#Hchan, -, Hoc⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(errMsg_ptr ↦□ go!"operation timed out") γ ch
    $$ Hchan Hoc with Hown
  ihave #Hdone_bc := ownBroadcastChan_Unknown _ _ _ _ $$ Hown
  ipersist done
  wp_apply wp_fork $$ [Hown errMsg]
  · wp_auto
    wp_apply time.wp_Sleep
    ipersist errMsg
    wp_apply wp_broadcast_chan_close (ty := go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType []))
      ch γ _ $$ [$Hown $errMsg] as -
    itrivial
  wp_apply wp_HelloWorldCancellable $$ [$Hdone_bc] as %result %Hres
  iapply HΦ
  ipureintro
  rcases Hres with h | h <;> simp [h]

theorem wp_CancellableHedgedRequest (query : GoString) (hedgeThreshold : time.Duration)
    (errStr_ptr' : Loc) (done_ch : chan.t) (γdone : ChanNames) :
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
        iprop(errStr_ptr' ↦ go!"cancelled" ∗ ⌜v = go!"" ∧ b = false⌝) }} := by
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
  wp_apply +noauto time.wp_After
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

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
