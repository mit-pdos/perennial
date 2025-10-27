From New.golang.defn Require Export chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base chan_au_send chan_au_recv chan_au_sel.
From iris.base_logic Require Export lib.ghost_var.
From New.golang.theory Require Import exception list mem loop typing struct proofmode pkg auto.
From Perennial Require Import base.

Set Default Proof Using "Type".

Module chan.

#[local] Transparent chan.make chan.receive chan.send chan.close
  chan.len chan.cap
  chan.for_range chan.select_nonblocking chan.select_blocking.

Section proof.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Lemma wp_make (cap: Z) {B: BoundedTypeSize t} :
  0 ≤ cap < 2^63 ->
  {{{ is_pkg_init channel }}}
    chan.make #t #(W64 cap)
  {{{ (ch: loc) (γ: chan_names), RET #ch;
      is_channel ch cap γ ∗
      own_channel ch cap (if decide (cap = 0) then chan_rep.Idle else chan_rep.Buffered []) γ
  }}}.
Proof.
  intros Hcap.
  wp_start.
  wp_call.
  wp_apply wp_NewChannel; first done.
  iFrame.
Qed.

Lemma wp_send (ch: loc) (cap: Z) (v: V) (γ: chan_names):
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ send_au_slow ch cap v γ (Φ #())) -∗
  WP chan.send #t #ch #v {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_call.
  wp_apply (wp_Send with "[$]").
  iFrame.
Qed.

Lemma wp_close (ch: loc) (cap: Z) (γ: chan_names):
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ close_au ch cap γ (Φ #())) -∗
  WP chan.close #t #ch {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_call.
  wp_apply (wp_Close with "[$]").
  iFrame.
Qed.

Lemma wp_receive (ch: loc) (cap: Z) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ rcv_au_slow ch cap γ (λ v ok, Φ (#v, #ok)%V)) -∗
  WP chan.receive #t #ch {{ Φ }}.
Proof.
  wp_start as "#Hch".
  wp_call.
  wp_apply (wp_Receive with "[$]").
  iFrame.
Qed.

End proof.

End chan.
