/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_higher_order.v`:
worker goroutines run closures received over a channel and send the result back
over a per-request future channel.

Lean notes:
* The channel ghost state needs `Pos.Countable request.t`; it is derived here
  from the countability of `func.t` and `loc` (`Perennial/GooseLang/Countable.lean`).
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel_examples_init
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Golang.Theory.Chan.Idioms.Future

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

instance request_countable [FfiSyntax] : Pos.Countable request.t :=
  countableOfLeftInverse (fun r : request.t => (r.f', r.result')) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

def doRequest (r : request.t) (γfut : FutureNames) (Q : GoString → IProp GF) : IProp GF :=
  iprop("Hf" ∷ WP (App (Val #r.f') (Val #())) {{ fun v => iprop(∃ s : GoString, ⌜v = #s⌝ ∗ Q s) }} ∗
    "#Hfut" ∷ isFuture GoString γfut r.result' ∗
    "Hpromise" ∷ Fulfill (V := GoString) γfut Q)

def awaitRequest (r : request.t) (γfut : FutureNames) (Q : GoString → IProp GF) : IProp GF :=
  iprop("#Hfut" ∷ isFuture GoString γfut r.result' ∗
    "HAwait" ∷ Await (V := GoString) γfut [Q])

set_option goose.wp.extras true

theorem wp_mkRequest (f : func.t) (Q : GoString → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        WP (App (Val #f) (Val #())) {{ fun v => iprop(∃ s : GoString, ⌜v = #s⌝ ∗ Q s) }} }}
      (App (Val (@! mkRequest)) (Val #f))
    {{ (γfut : FutureNames) (r : request.t), RET #r;
        doRequest r γfut Q ∗ awaitRequest r γfut Q }} := by
  wp_start as Hf
  wp_auto
  iapply wp_fupd
  wp_apply chan.wp_make2 (V := GoString) (W64 1) $$ [] as %ch %γ ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; decide
  imod start_future (V := GoString) ch γ (.Buffered []) (.inr rfl) $$ Hch Hown
    with ⟨%γfut, #Hfut, HAwait⟩
  imod future_alloc_promise (V := GoString) γfut ch Q [] $$ Hfut HAwait with ⟨Hpromise, HAwait⟩
  imodintro
  iapply HΦ
  unfold doRequest awaitRequest
  iframe # ∗

omit package_sem in
theorem wp_get_response (r : request.t) (γfut : FutureNames) (Q : GoString → IProp GF) :
    {{ awaitRequest r γfut Q }}
      (App (Val (chan.receive go.string)) (Val #r.result'))
    {{ (s : GoString), RET (PairV #s #true); Q s }} := by
  iintro %Φ H HΦ
  unfold awaitRequest
  icases H with ⟨#Hfut, HAwait⟩
  iapply wp_future_await (t := go.string) γfut r.result' [Q] $$ [$Hfut $HAwait]
  inext
  iintro %v %P %pre %post ⟨%Hsplit, HP, -⟩
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at Hsplit
    obtain ⟨rfl, -⟩ := Hsplit
    iapply HΦ $$ HP
  | cons a pre' =>
    have := congrArg List.length Hsplit
    simp at this


def isRequestChan (γ : ChanNames) (ch : Loc) : IProp GF :=
  isChanBag (V := request.t) γ ch (fun r => iprop(∃ γfut Q, doRequest r γfut Q))

instance isRequestChan_pers (γ : ChanNames) (ch : Loc) :
    Persistent (isRequestChan (GF := GF) γ ch) := by
  unfold isRequestChan; infer_instance

theorem wp_ho_worker (γ : ChanNames) (ch : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isRequestChan γ ch }}
      (App (Val (@! ho_worker)) (Val #ch))
    {{ RET #(); True }} := by
  wp_start as #His
  unfold isRequestChan at *
  wp_auto
  ihave HI : (∃ r0 : request.t, "r" ∷ r_ptr ↦ r0 : IProp GF) $$ [r]
  · iexists _; iexact r
  wp_for HI
  wp_apply wp_bag_receive (t := request) γ ch _ $$ His as %rq Hreq
  icases Hreq with ⟨%γfut, %Q, Hreq⟩
  unfold doRequest
  iNamed Hreq
  wp_bind (App (Val #rq.f') (Val #()))
  iapply wp_wand $$ Hf
  iintro %v ⟨%s, %Hv, HQ⟩
  subst Hv
  wp_auto
  wp_apply wp_future_fulfill (t := go.string) γfut rq.result' s $$ [$Hfut Hpromise HQ]
  · unfold Fulfilled; iexists Q; iframe
  wp_for_post
  iframe
  iexists rq
  iexact r

set_option maxHeartbeats 400000 in
theorem wp_HigherOrderExample :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! HigherOrderExample)) (Val #()))
    {{ (s : slice.t), RET #s; s ↦* [go!"hello world", go!"HELLO", go!"world"] }} := by
  wp_start
  wp_auto
  iapply wp_fupd
  wp_apply chan.wp_make1 (V := request.t) $$ [] as %req_ch %γ ⟨#His, %Hcap, Hown⟩
  imod start_bag (fun r => iprop(∃ γfut Q, doRequest r γfut Q)) _ req_ch γ trivial $$ His Hown
    with #Hch
  ihave #Hreqs : isRequestChan γ req_ch $$ []
  · unfold isRequestChan; iexact Hch
  ipersist c
  wp_apply wp_fork $$ []
  · wp_apply wp_ho_worker $$ [$Hreqs]
    itrivial
  wp_apply wp_fork $$ []
  · wp_apply wp_ho_worker $$ [$Hreqs]
    itrivial
  wp_apply wp_mkRequest _ (fun s => iprop(⌜s = go!"hello world"⌝)) $$ [] as %γfut1 %r1 ⟨Hdo1, Hawait1⟩
  · wp_auto
    iexists _
    ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_mkRequest _ (fun s => iprop(⌜s = go!"HELLO"⌝)) $$ [] as %γfut2 %r2 ⟨Hdo2, Hawait2⟩
  · wp_auto
    iexists _
    ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_mkRequest _ (fun s => iprop(⌜s = go!"world"⌝)) $$ [] as %γfut3 %r3 ⟨Hdo3, Hawait3⟩
  · wp_auto
    iexists _
    ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_bag_send (t := request) γ req_ch r1 _ $$ [$Hch Hdo1]
  · iexists _, _; iexact Hdo1
  wp_apply wp_bag_send (t := request) γ req_ch r2 _ $$ [$Hch Hdo2]
  · iexists _, _; iexact Hdo2
  wp_apply wp_bag_send (t := request) γ req_ch r3 _ $$ [$Hch Hdo3]
  · iexists _, _; iexact Hdo3
  wp_apply wp_get_response r1 γfut1 _ $$ Hawait1 as %s1 %Hs1
  wp_apply wp_get_response r2 γfut2 _ $$ Hawait2 as %s2 %Hs2
  wp_apply wp_get_response r3 γfut3 _ $$ Hawait3 as %s3 %Hs3
  subst Hs1 Hs2 Hs3
  wp_apply wp_slice_literal (V := GoString) [go!"hello world", go!"HELLO", go!"world"]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  imodintro
  iapply HΦ $$ Hsl
end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
