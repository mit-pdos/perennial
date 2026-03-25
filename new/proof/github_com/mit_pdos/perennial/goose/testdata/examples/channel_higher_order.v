From New.proof.github_com.mit_pdos.perennial.goose.testdata.examples Require Import channel_examples_init.
From New.golang.theory.chan.idioms
  Require Import base bag future.
From New.code Require Import github_com.mit_pdos.perennial.goose.testdata.examples.channel.
Import channel_examples.
From New.golang Require Import theory.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : channel_examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Section higher_order_example.

Definition do_request (r: request.t) γfut (Q: go_string → iProp Σ) : iProp Σ :=
  "Hf" ∷ WP #r.(request.f') #() {{ λ v, ∃ (s: go_string), ⌜v = #s⌝ ∗ Q s }} ∗
  "#Hfut" ∷ is_future (V:=go_string)  γfut r.(request.result') ∗
  "Hpromise" ∷ Fulfill (V:=go_string)  γfut Q.

Definition await_request (r: request.t) γfut (Q: go_string → iProp Σ) : iProp Σ :=
  "#Hfut" ∷ is_future (V:=go_string) γfut r.(request.result') ∗
  "HAwait" ∷ Await (V:=go_string) γfut [Q].

Lemma wp_mkRequest {f: func.t} (Q: go_string → iProp Σ) :
  {{{ is_pkg_init channel_examples ∗ WP #f #() {{ λ v, ∃ (s: go_string), ⌜v = #s⌝ ∗ Q s }} }}}
    @! channel_examples.mkRequest #f
  {{{ γfut (r: request.t), RET #r; do_request r γfut Q ∗ await_request r γfut Q }}}.
  Proof using All.
  wp_start as "Hf".
  wp_auto.
  wp_apply chan.wp_make2; first done.
  iIntros (ch γ) "(His & _Hcap & Hown)".
  simpl.
  iMod (start_future (V:=go_string)  (t:=go.string) ch γ (chanstate.Buffered []) with "[$His] [$Hown]") as (γfuture) "(#Hfut & HAwait)".
  { right. done. }
  iMod (future_alloc_promise (V:=go_string) (t:=go.string) γfuture ch Q [] with "Hfut HAwait") as "(Hpromise & HAwait)".
  wp_auto.
  iApply "HΦ".
  iFrame "Hfut Hf Hpromise HAwait".
Qed.

#[local] Lemma wp_get_response r γfut Q :
  {{{ await_request r γfut Q }}}
    chan.receive go.string #r.(channel_examples.request.result')
  {{{ (s: go_string), RET (#s, #true); Q s }}}.
  Proof using All.

  wp_start as "Hawait". iNamed "Hawait".
  wp_apply (wp_future_await with "[$Hfut $HAwait]").
  iIntros (v P pre post) "(%Hsplit & HP & _HAwait)".
  destruct pre as [|? pre']; simpl in Hsplit.
  - injection Hsplit as <-.
    destruct post as [|? post']; last done.
    iApply "HΦ". iFrame.
  -  iApply "HΦ". exfalso.
    assert (length [Q] = length (u :: pre' ++ P :: post)) as Hlen by (rewrite Hsplit; done).
    simpl in Hlen.
    rewrite app_length in Hlen.
    simpl in Hlen.
    lia.
Qed.

Definition is_request_chan γ (ch: loc): iProp Σ :=
  is_chan_bag (V:=channel_examples.request.t) γ ch (λ r, ∃ γfut Q, do_request r γfut Q)%I.

Lemma wp_ho_worker γ ch :
  {{{ is_pkg_init channel_examples ∗ is_request_chan γ ch }}}
    @! channel_examples.ho_worker #ch
  {{{ RET #(); True }}}.
  Proof using All.
  wp_start as "#His".
  rewrite /is_request_chan.
  wp_auto.
  iAssert (∃ (r0: channel_examples.request.t),
      "r" ∷ r_ptr ↦ r0
    )%I with "[$r]" as "IH".
  wp_for "IH".
  wp_apply (wp_bag_receive with "[$His]") as "%r Hreq".
  iNamed "Hreq".
  wp_bind.
  iApply (wp_wand with "[Hf]").
  { iApply "Hf". }
  iIntros (v) "HQ".
  iDestruct "HQ" as (s) "[-> HQ]".
  wp_auto.
  wp_apply (wp_future_fulfill with "[$Hfut $Hpromise HQ]").
  { done. }
  wp_for_post.
  iFrame.
Qed.

Lemma wp_HigherOrderExample :
  {{{ is_pkg_init channel_examples }}}
    @! channel_examples.HigherOrderExample #()
  {{{ (s:slice.t), RET #s; s ↦* ["hello world"%go; "HELLO"%go; "world"%go] }}}.
  Proof using All.
  wp_start.
  wp_auto.
  wp_apply chan.wp_make1.
  iIntros (req_ch γ) "(His & _Hcap & Hown)".
  simpl.
  iMod (start_bag with "His Hown") as "#Hch".
  { done. }
  iAssert (is_request_chan γ req_ch) with "[$Hch]" as "#Hreqs".
  wp_auto.
  wp_apply (wp_fork).
  {
    wp_apply (wp_ho_worker).
    { iFrame "#". }
    done.
  }
  wp_apply (wp_fork).
  {
    wp_apply (wp_ho_worker).
    { iFrame "#". }
    done.
  }
  wp_apply (wp_mkRequest (λ s, ⌜s = "hello world"%go⌝)%I) as "%γfut1 %r1 [Hdo_r1 Hawait_r1]".
  {
    wp_auto.
    eauto.
  }
  wp_apply (wp_mkRequest (λ s, ⌜s = "HELLO"%go⌝)%I) as "%γfut2 %r2 [Hdo_r2 Hawait_r2]".
  {
    wp_auto.
    eauto.
  }
  wp_apply (wp_mkRequest (λ s, ⌜s = "world"%go⌝)%I) as "%γfut3 %r3 [Hdo_r3 Hawait_r3]".
  {
    wp_auto.
    eauto.
  }
  wp_apply (wp_bag_send with "[$Hch $Hdo_r1]").
  wp_apply (wp_bag_send with "[$Hch $Hdo_r2]").
  wp_apply (wp_bag_send with "[$Hch $Hdo_r3]").
  wp_apply (wp_get_response with "[$Hawait_r1]") as "%s %Heq".
  subst.
  wp_apply (wp_get_response with "[$Hawait_r2]") as "%s %Heq".
  subst.
  wp_apply (wp_get_response with "[$Hawait_r3]") as "%s %Heq".
  subst.
  wp_apply wp_slice_literal.
  { iIntros. wp_auto. iFrame. }
  iIntros (sl) "Hresponse".
  wp_auto.
  iApply "HΦ".
  done.
Qed.

End higher_order_example.
End proof.
