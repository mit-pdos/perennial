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

instance Result.countable [ffi_syntax] : Pos.Countable Result.t :=
  .ofInjective (fun r => Pos.Countable.encode (r.value', r.primary_won'))
    (by rintro ⟨a, b⟩ ⟨c, d⟩ h; have h := Pos.encode_inj h; simp_all)

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

/-! ### Hedged requests -/

theorem wp_GetPrimary (q : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! GetPrimary)) (Val #q))
    {{ RET #(q ++ go!"_primary.html"); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_GetSecondary (q : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! GetSecondary)) (Val #q))
    {{ RET #(q ++ go!"_secondary.html"); True }} := by
  wp_start
  wp_auto
  wp_end

/-! ### Hello world -/

theorem wp_sys_hello_world :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! sys_hello_world)) (Val #()))
    {{ RET #(go!"Hello, World!"); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_HelloWorldAsync :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! HelloWorldAsync)) (Val #()))
    {{ (ch : loc) (γfut : chan_names), RET #ch;
        is_chan ch γfut go_string ∗
        is_chan_bag γfut ch (fun (v : go_string) => iprop(⌜v = go!"Hello, World!"⌝)) }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := go_string) $$ [] as %ch %γ ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  rw [if_neg (by decide)]
  imod start_bag (fun (v : go_string) => iprop(⌜v = go!"Hello, World!"⌝)) _ ch γ trivial $$ Hch Hoc
    with #Hbag
  wp_auto
  ipersist ch
  wp_apply wp_fork $$ []
  · wp_auto
    wp_apply wp_sys_hello_world
    wp_apply wp_bag_send γ ch _ _ $$ [$Hbag]
    · ipureintro; rfl
    itrivial
  wp_auto
  iapply HΦ
  iframe #

theorem wp_HelloWorldSync :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! HelloWorldSync)) (Val #()))
    {{ RET #(go!"Hello, World!"); True }} := by
  wp_start
  wp_apply wp_HelloWorldAsync as %ch %γ ⟨#Hch, #Hbag⟩
  wp_apply wp_bag_receive γ ch _ $$ Hbag as %v %Hv
  subst Hv
  wp_end

/-! ### Joins -/

theorem wp_simple_join :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! simple_join)) (Val #()))
    {{ RET #(go!"Hello, World!"); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := Unit) $$ [] as %ch %γ ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  rw [if_neg (by decide)]
  wp_auto
  imod start_future (V := Unit) (t := go.type.StructType []) ch γ _ (.inr rfl) $$ Hch Hoc
    with ⟨%γfut, #Hfut, HAwait⟩
  imod future_alloc_promise (V := Unit) (t := go.type.StructType []) γfut ch
    (fun _ => iprop(message_ptr ↦ go!"Hello, World!")) [] $$ Hfut HAwait with ⟨Hpromise, HAwait⟩
  ipersist ch
  wp_apply wp_fork $$ [Hpromise message]
  · wp_auto
    wp_apply wp_future_fulfill (t := go.type.StructType []) γfut ch () $$ [$Hfut Hpromise message]
    · unfold Fulfilled; iexists _; iframe
    itrivial
  wp_apply wp_future_await (t := go.type.StructType []) γfut ch _ $$ [$Hfut $HAwait]
    as %v %P %pre %post ⟨%Hsplit, HP, -⟩
  rcases pre with _ | ⟨_, pre⟩
  · simp only [List.nil_append, List.cons.injEq] at Hsplit
    obtain ⟨rfl, -⟩ := Hsplit
    wp_auto
    wp_end
  · simp at Hsplit

theorem wp_simple_multi_join :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! simple_multi_join)) (Val #()))
    {{ RET #(go!"Hello World"); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := Unit) $$ [] as %ch %γ ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  rw [if_neg (by decide)]
  wp_auto
  imod start_future (V := Unit) (t := go.type.StructType []) ch γ _ (.inr rfl) $$ Hch Hoc
    with ⟨%γfut, #Hfut, HAwait⟩
  imod future_alloc_promise (V := Unit) (t := go.type.StructType []) γfut ch
    (fun _ => iprop(hello_ptr ↦ go!"Hello")) [] $$ Hfut HAwait with ⟨Hpromise1, HAwait⟩
  imod future_alloc_promise (V := Unit) (t := go.type.StructType []) γfut ch
    (fun _ => iprop(world_ptr ↦ go!"World")) _ $$ Hfut HAwait with ⟨Hpromise2, HAwait⟩
  ipersist ch
  wp_apply wp_fork $$ [Hpromise1 hello]
  · wp_auto
    wp_apply wp_future_fulfill (t := go.type.StructType []) γfut ch () $$ [$Hfut Hpromise1 hello]
    · unfold Fulfilled; iexists _; iframe
    itrivial
  wp_apply wp_fork $$ [Hpromise2 world]
  · wp_auto
    wp_apply wp_future_fulfill (t := go.type.StructType []) γfut ch () $$ [$Hfut Hpromise2 world]
    · unfold Fulfilled; iexists _; iframe
    itrivial
  wp_apply wp_future_await (t := go.type.StructType []) γfut ch _ $$ [$Hfut $HAwait]
    as %v1 %P1 %pre1 %post1 ⟨%Hsplit1, HP1, HAwait⟩
  -- which contract was fulfilled first
  rcases pre1 with _ | ⟨_, _ | ⟨_, pre1⟩⟩
  · simp only [List.nil_append, List.cons.injEq] at Hsplit1
    obtain ⟨rfl, rfl⟩ := Hsplit1
    wp_apply wp_future_await (t := go.type.StructType []) γfut ch _ $$ [$Hfut $HAwait]
      as %v2 %P2 %pre2 %post2 ⟨%Hsplit2, HP2, -⟩
    rcases pre2 with _ | ⟨_, pre2⟩
    · simp only [List.nil_append, List.cons.injEq] at Hsplit2
      obtain ⟨rfl, -⟩ := Hsplit2
      wp_auto
      wp_end
    · simp at Hsplit2
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at Hsplit1
    obtain ⟨rfl, rfl, rfl⟩ := Hsplit1
    wp_apply wp_future_await (t := go.type.StructType []) γfut ch _ $$ [$Hfut $HAwait]
      as %v2 %P2 %pre2 %post2 ⟨%Hsplit2, HP2, -⟩
    rcases pre2 with _ | ⟨_, pre2⟩
    · simp only [List.nil_append, List.cons.injEq] at Hsplit2
      obtain ⟨rfl, -⟩ := Hsplit2
      wp_auto
      wp_end
    · simp at Hsplit2
  · simp at Hsplit1

/-! ### Exchanging pointers through a handshake -/

theorem wp_exchangePointer :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! exchangePointer)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#Hch, -, Hoc⟩
  wp_auto
  imod start_handshake (V := Unit) (t := go.type.StructType []) ch (fun _ => iprop(x_ptr ↦ W64 1))
    iprop(y_ptr ↦ W64 2) γ $$ Hch Hoc with #H
  ipersist ch
  wp_apply wp_fork $$ [x]
  · wp_auto
    wp_apply wp_handshake_send (t := go.type.StructType []) γ ch () _ _ $$ [$H $x] as y
    itrivial
  wp_apply wp_handshake_receive (t := go.type.StructType []) γ ch _ _ $$ [$H $y] as %v x
  wp_end

/-! ### Broadcast -/

theorem wp_BroadcastExample :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! BroadcastExample)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %done_ch %γdone ⟨#Hdone_ch, -, Hdone_own⟩
  wp_auto
  wp_apply chan.wp_make1 (V := w64) as %result1_ch %γr1 ⟨#Hr1_ch, -, Hr1_own⟩
  wp_auto
  wp_apply chan.wp_make1 (V := w64) as %result2_ch %γr2 ⟨#Hr2_ch, -, Hr2_own⟩
  wp_auto
  imod start_bag (fun (v : w64) => iprop(⌜v = W64 6⌝)) _ result1_ch γr1 trivial $$ Hr1_ch Hr1_own
    with #Hbag1
  imod start_bag (fun (v : w64) => iprop(⌜v = W64 10⌝)) _ result2_ch γr2 trivial $$ Hr2_ch Hr2_own
    with #Hbag2
  imod alloc_broadcast_chan (E := ⊤) iprop(sharedValue_ptr ↦□ W64 2) γdone done_ch
    $$ Hdone_ch Hdone_own with Hown_done
  ihave #Hdone_bc := own_broadcast_chan_Unknown _ _ _ _ $$ Hown_done
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
  wp_apply wp_broadcast_chan_close (ty := go.type.ChannelType go.chan_dir.sendrecv (go.type.StructType []))
    done_ch γdone _ $$ [$Hown_done $sharedValue] as -
  wp_apply wp_bag_receive γr1 result1_ch _ $$ Hbag1 as %v1 %Hv1
  subst Hv1
  wp_apply wp_bag_receive γr2 result2_ch _ $$ Hbag2 as %v2 %Hv2
  subst Hv2
  wp_auto
  wp_end

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
