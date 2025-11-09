From New.golang.defn Require Export chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base chan_au_send chan_au_recv.
From iris.base_logic Require Export lib.ghost_var.
From New.golang.theory Require Import exception list mem loop typing struct proofmode pkg auto.
From Perennial Require Import base.

Open Scope Z_scope.

Set Default Proof Using "Type".

Module chan.

#[local] Transparent chan.make chan.receive chan.send chan.close
  chan.len chan.cap
  chan.for_range chan.select_nonblocking chan.select_blocking.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Lemma wp_make (cap: Z) {B: BoundedTypeSize t} :
  0 ≤ cap < 2^63 ->
  {{{ True }}}
    chan.make #t #(W64 cap)
  {{{ (ch: loc) (γ: chan_names), RET #ch;
      is_channel ch γ ∗
      chan_cap γ cap ∗
      own_channel ch (if decide (cap = 0) then chan_rep.Idle else chan_rep.Buffered []) γ
  }}}.
Proof.
  intros Hcap.
  wp_start.
  wp_call.
  wp_apply wp_NewChannel; first done.
  iFrame.
Qed.

Lemma wp_send (ch: loc) (v: V) (γ: chan_names):
  ∀ Φ,
  is_channel ch γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ send_au_slow ch v γ (Φ #())) -∗
  WP chan.send #t #ch #v {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_call.
  wp_apply (wp_Send with "[$]").
  iFrame.
Qed.

Lemma wp_close (ch: loc) (γ: chan_names):
  ∀ Φ,
  is_channel ch γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ close_au ch γ (Φ #())) -∗
  WP chan.close #t #ch {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_call.
  wp_apply (wp_Close with "[$]").
  iFrame.
Qed.

Lemma wp_receive (ch: loc) (γ: chan_names) :
  ∀ Φ,
  is_channel ch γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ rcv_au_slow ch γ (λ v ok, Φ (#v, #ok)%V)) -∗
  WP chan.receive #t #ch {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_call.
  wp_apply (wp_Receive with "[$]").
  iFrame.
Qed.

Lemma wp_cap (ch: loc) (γ: chan_names) :
  {{{ is_channel ch γ }}}
    chan.cap #t #ch
  {{{ (cap: Z), RET #(W64 cap); chan_cap γ cap }}}.
Proof.
  wp_start as "#Hch".
  wp_call.
  iDestruct (is_channel_get_cap with "Hch") as (cap) "Hcap".
  wp_apply (wp_Cap with "[$Hch]").
  { iFrame "#". }
  by iApply "HΦ".
Qed.

Inductive op :=
| select_send_f (t: go_type) (v : val) (ch : chan.t) (handler : func.t)
| select_receive_f (t: go_type) (ch : chan.t) (handler : func.t).

Global Instance into_val_op : IntoVal op :=
  {|
    to_val_def := λ o,
        match o with
        | select_send_f t v ch f => InjLV (#t, #ch, v, #f)
        | select_receive_f t ch f => InjRV (#t, #ch, #f)
        end
  |}.

Global Instance wp_select_send ch (v : val) f :
  PureWp True (chan.select_send #t #ch v #f)
    #(select_send_f t v ch f).
Proof.
  pure_wp_start. repeat rewrite to_val_unseal /=. by iApply "HΦ".
Qed.

Global Instance wp_select_receive ch f :
  PureWp True (chan.select_receive #t #ch #f)
    #(select_receive_f t ch f).
Proof.
  pure_wp_start. repeat rewrite to_val_unseal /=. by iApply "HΦ".
Qed.

Lemma wp_select_blocking (cases : list op) :
  ∀ Φ,
  ([∧ list] case ∈ cases,
     match case with
     | select_send_f t send_val send_chan send_handler =>
         ∃ V γ (v : V) `(!IntoVal V) `(!chanG Σ V) `(!IntoValTyped V t),
             ⌜ send_val = #v ⌝ ∗
             is_channel (V:=V) (t:=t) send_chan γ ∗
             send_au_slow send_chan v γ (WP #send_handler #() {{ Φ }})
     | select_receive_f t recv_chan recv_handler =>
         ∃ γ V `(!IntoVal V) `(!IntoValTyped V t) `(!chanG Σ V),
             is_channel (V:=V) (t:=t) recv_chan γ ∗
             rcv_au_slow recv_chan γ (λ (v: V) ok,
               WP #recv_handler (#v, #ok)%V {{ Φ }})
     end
  ) -∗
  WP chan.select_blocking #cases {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases".
  iLöb as "IH".
  wp_call.
Admitted.

Lemma wp_select_nonblocking (cases : list op) (def: func.t) :
  ∀ Φ,
  ([∧ list] case ∈ cases,
     match case with
     | select_send_f t send_val send_chan send_handler =>
         ∃ V γ (v : V) `(!IntoVal V) `(!chanG Σ V) `(!IntoValTyped V t),
             ⌜ send_val = #v ⌝ ∗
             is_channel (V:=V) (t:=t) send_chan γ ∗
             send_au_fast send_chan v γ (WP #send_handler #() {{ Φ }})
     | select_receive_f t recv_chan recv_handler =>
         ∃ γ V `(!IntoVal V) `(!IntoValTyped V t) `(!chanG Σ V),
             is_channel (V:=V) (t:=t) recv_chan γ ∗
             rcv_au_fast recv_chan γ (λ (v: V) ok,
               WP #recv_handler #v {{ Φ }})
     end
  ) ∧ WP #def #() {{ Φ }} -∗
  WP chan.select_nonblocking #cases #def {{ Φ }}.
Proof.
  iIntros (Φ) "Hcases".
  wp_call.
Admitted.

End proof.

End chan.
