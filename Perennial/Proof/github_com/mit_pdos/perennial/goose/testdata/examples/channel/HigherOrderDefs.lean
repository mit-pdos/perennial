/-
Worker goroutines run closures received over a channel and send the result back
over a per-request future channel.

The channel ghost state needs `Pos.Countable request.t`; it is derived here
from the countability of `GoFunc` and `loc` (`Perennial/GooseLang/Countable.lean`).

This file: the request predicates and the receive of a
response (`wp_get_response`, a `chan.receive`, not a Go function).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

instance request_countable [FfiSyntax] : Pos.Countable request :=
  countableOfLeftInverse (fun r : request => (r.f', r.result')) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

def doRequest (r : request) (γfut : FutureNames) (Q : GoString → IProp GF) : IProp GF :=
  iprop("Hf" ∷ WP (App (Val #r.f') (Val #())) {{ fun v => iprop(∃ s : GoString, ⌜v = #s⌝ ∗ Q s) }} ∗
    "#Hfut" ∷ isFuture GoString γfut r.result' ∗
    "Hpromise" ∷ Fulfill (V := GoString) γfut Q)

def awaitRequest (r : request) (γfut : FutureNames) (Q : GoString → IProp GF) : IProp GF :=
  iprop("#Hfut" ∷ isFuture GoString γfut r.result' ∗
    "HAwait" ∷ Await (V := GoString) γfut [Q])

omit package_sem in
theorem wp_get_response (r : request) (γfut : FutureNames) (Q : GoString → IProp GF) :
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
  isChanBag (V := request) γ ch (fun r => iprop(∃ γfut Q, doRequest r γfut Q))

instance isRequestChan_pers (γ : ChanNames) (ch : Loc) :
    Persistent (isRequestChan (GF := GF) γ ch) := by
  unfold isRequestChan; infer_instance

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
